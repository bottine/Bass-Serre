import category_theory.path_category
import category_theory.quotient
import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv 
import data.set.lattice
import combinatorics.quiver.connected_component
import group_theory.subgroup.basic

/-
path_category == the free category of pats
quotient == quotienting morphisms by relations
algebra.hom.equiv to use ≃*
-/

open set
open classical function
local attribute [instance] prop_decidable


namespace category_theory
namespace groupoid
namespace free

variable {V : Type*}
variable (Q : quiver V)

inductive word : V → V → Sort*
| nil {c : V} : word c c
| cons_p {c d e : V} (p : Q.hom c d) (w : word d e) : word c e
| cons_n {c d e : V} (p : Q.hom d c) (w : word d e) : word c e

variable {Q}

def word.length : Π {c d : V}, word Q c d → ℕ
| _ _ word.nil := 0
| _ _ (word.cons_p _ t) := t.length.succ
| _ _ (word.cons_n _ t) := t.length.succ 

lemma word.length_cast : Π {c c' d : V} (w : word Q c d) (e : c = c'), w.length = (e.rec_on w).length :=
by {rintros _ _ _ w e, induction e, simp, }

@[pattern]
def word.letter_p {c d : V} (p : Q.hom c d) : word Q c d := (word.cons_p p word.nil)
@[pattern]
def word.letter_n {c d : V} (p : Q.hom c d) : word Q d c := (word.cons_n p word.nil)

def word.append  : Π {c d e : V}, word Q c d → word Q d e → word Q c e
| _ _ _ (word.nil) w := w
| _ _ _ (word.cons_p p u) w := word.cons_p p (u.append w)
| _ _ _ (word.cons_n p u) w := word.cons_n p (u.append w)

@[simp] lemma word.append_assoc {c d e f : V} {p : word Q c d} {q : word Q d e} {r : word Q e f} : (p.append q).append r = p.append (q.append r) := sorry

infix ` ≫* `:50 := word.append

def word.reverse : Π {c d : V}, word Q c d → word Q d c
| _ _ (word.nil) := word.nil
| _ _ (word.cons_p p u) := (u.reverse.append (word.letter_n p))
| _ _ (word.cons_n p u) := (u.reverse.append (word.letter_p p))

def word.is_head_reduced : Π {c d : V}, word Q c d → Prop 
| _ _ (word.nil) := true
| _ _ (word.letter_p _) := true 
| _ _ (word.letter_n _) := true 
| _ _ (@word.cons_p _ _ x y z p (@word.cons_n _ _ .(y) w .(z) q tail)) := ¬ (∃ e : x = w, e.rec_on p = q)
| _ _ (@word.cons_n _ _ x y z p (@word.cons_p _ _ .(y) w .(z) q tail)) := ¬ (∃ e : x = w, e.rec_on p = q)
| _ _ (word.cons_p p (word.cons_p q tail)) := true
| _ _ (word.cons_n p (word.cons_n q tail)) := true

def word.is_reduced : Π {c d : V}, word Q c d → Prop 
| _ _ (word.nil) := true
| _ _ (word.letter_p _) := true 
| _ _ (word.letter_n _) := true 
| _ _ (word.cons_p p (word.cons_n q tail)) := (word.cons_p p (word.cons_n q tail)).is_head_reduced ∧ (word.cons_n q tail).is_reduced
| _ _ (word.cons_n p (word.cons_p q tail)) := (word.cons_n p (word.cons_p q tail)).is_head_reduced ∧ (word.cons_p q tail).is_reduced
| _ _ (word.cons_p p (word.cons_p q tail)) := (word.cons_p p (word.cons_p q tail)).is_head_reduced ∧ (word.cons_p q tail).is_reduced
| _ _ (word.cons_n p (word.cons_n q tail)) := (word.cons_n p (word.cons_n q tail)).is_head_reduced ∧ (word.cons_n q tail).is_reduced

noncomputable def word.head_reduce : Π {c d : V}, word Q c d → word Q c d
| _ _ (word.nil) := word.nil
| _ _ (word.letter_p p) := word.letter_p p 
| _ _ (word.letter_n p) := word.letter_n p
| _ _ (@word.cons_p _ _ x y z p (@word.cons_n _ _ .(y) w .(z) q tail)) := 
  if h : (∃ e : x = w, e.rec_on p = q) then eq.rec_on h.some.symm tail else (word.cons_p p (word.cons_n q tail))
| _ _ (@word.cons_n _ _ x y z p (@word.cons_p _ _ .(y) w .(z) q tail)) := 
  if h : (∃ e : x = w, e.rec_on p = q) then eq.rec_on h.some.symm tail else (word.cons_n p (word.cons_p q tail))
| _ _ (word.cons_p p (word.cons_p q tail)) := (word.cons_p p (word.cons_p q tail))
| _ _ (word.cons_n p (word.cons_n q tail)) := (word.cons_n p (word.cons_n q tail))

noncomputable def word.reduce : Π {c d : V}, word Q c d → word Q c d
| _ _ (word.nil) := word.nil
| _ _ (word.letter_p p) := word.letter_p p 
| _ _ (word.letter_n p) := word.letter_n p
| _ _ (@word.cons_p _ _ x y z p (@word.cons_n _ _ .(y) w .(z) q tail)) := 
  if h : (∃ e : x = w, e.rec_on p = q) then eq.rec_on h.some.symm tail.reduce else (word.cons_p p (word.cons_n q tail).reduce).head_reduce
| _ _ (@word.cons_n _ _ x y z p (@word.cons_p _ _ .(y) w .(z) q tail)) := 
  if h : (∃ e : x = w, e.rec_on p = q) then eq.rec_on h.some.symm tail.reduce else (word.cons_n p (word.cons_p q tail).reduce).head_reduce
| _ _ (word.cons_p p (word.cons_p q tail)) := (word.cons_p p (word.cons_p q tail).reduce).head_reduce
| _ _ (word.cons_n p (word.cons_n q tail)) := (word.cons_n p (word.cons_n q tail).reduce).head_reduce

postfix ` ↓ `:100 := word.reduce

lemma word.is_head_reduced_iff_head_reduce_eq : Π {c d : V} (w : word Q c d), w.is_head_reduced ↔ w.head_reduce = w
| _ _ (word.nil) := by {dsimp [word.head_reduce,word.is_head_reduced], simp only,}
| _ _ (word.letter_p _) := by {dsimp [word.head_reduce,word.is_head_reduced], simp,}
| _ _ (word.letter_n _) := by {dsimp [word.head_reduce,word.is_head_reduced], simp,}
| _ _ (@word.cons_p _ _ x y z p (@word.cons_n _ _ .(y) w .(z) q tail)) := 
  by 
  { dsimp [word.head_reduce,word.is_head_reduced], 
    simp only [not_exists, dite_eq_right_iff, forall_exists_index], 
    split, 
    { rintros h₁ h₂ h₃, exact (h₁ h₂ h₃).elim, }, 
    { rintro h₁ h₂ h₃, specialize h₁ h₂ h₃,
     let := congr_arg word.length h₁, rw ←word.length_cast at this, dsimp [word.length] at this, sorry} }
| _ _ (@word.cons_n _ _ x y z p (@word.cons_p _ _ .(y) w .(z) q tail)) :=
  by 
  { dsimp [word.head_reduce,word.is_head_reduced], 
    simp only [not_exists, dite_eq_right_iff, forall_exists_index], 
    split, 
    { rintros h₁ h₂ h₃, exact (h₁ h₂ h₃).elim, }, 
    { rintro h₁ h₂ h₃, specialize h₁ h₂ h₃, sorry, } } -- h₁ should be a contradiction, but not sure of the proper way to get it
| _ _ (word.cons_p p (word.cons_p q tail)) := by {dsimp [word.head_reduce,word.is_head_reduced], simp,}
| _ _ (word.cons_n p (word.cons_n q tail)) := by {dsimp [word.head_reduce,word.is_head_reduced], simp,}


lemma word.is_reduced_iff_reduce_eq : Π {c d : V} (w : word Q c d), w.is_reduced ↔ w.reduce = w
| _ _ (word.nil) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], simp only,}
| _ _ (word.letter_p _) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], simp,}
| _ _ (word.letter_n _) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], simp,}
| _ _ (@word.cons_p _ _ x y z p (@word.cons_n _ _ .(y) w .(z) q tail)) := by 
  { dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], 
    sorry, }
| _ _ (@word.cons_n _ _ x y z p (@word.cons_p _ _ .(y) w .(z) q tail)) :=
  by 
  { dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], sorry, }  -- h₁ should be a contradiction, but not sure of the proper way to get it
| _ _ (word.cons_p p (word.cons_p q tail)) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], sorry,}
| _ _ (word.cons_n p (word.cons_n q tail)) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], sorry,}

lemma word.reduce_is_reduced: Π {c d : V} (w : word Q c d), w.reduce.is_reduced := sorry

lemma word.reduce_idem {c d : V} (w : word Q c d) : w.reduce.reduce = w.reduce := 
begin 
  rw ←word.is_reduced_iff_reduce_eq (w.reduce),
  apply word.reduce_is_reduced,
end


lemma word.reverse_reduce_eq_reduce_reverse : Π {c d : V} (w : word Q c d), w.reverse.reduce = w.reduce.reverse
| _ _ (word.nil) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced,word.reverse], simp}
| _ _ (word.letter_p _) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], simp,}
| _ _ (word.letter_n _) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], simp,}
| _ _ (@word.cons_p _ _ x y z p (@word.cons_n _ _ .(y) w .(z) q tail)) := by 
  { dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], 
    sorry }
| _ _ (@word.cons_n _ _ x y z p (@word.cons_p _ _ .(y) w .(z) q tail)) :=
  by 
  { dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], sorry, }  -- h₁ should be a contradiction, but not sure of the proper way to get it
| _ _ (word.cons_p p (word.cons_p q tail)) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], sorry,}
| _ _ (word.cons_n p (word.cons_n q tail)) := by {dsimp [word.head_reduce,word.reduce,word.is_head_reduced,word.is_reduced], sorry,}

lemma word.reduce_both_append_reduce : Π {c d e : V} (u : word Q c d) (w : word Q d e), (u↓ ≫* w↓)↓ = (u ≫* w)↓ := sorry
lemma word.reduce_left_append_reduce : Π {c d e : V} (u : word Q c d) (w : word Q d e), (u↓ ≫* w)↓ = (u ≫* w)↓ := sorry
lemma word.reduce_right_append_reduce : Π {c d e : V} (u : word Q c d) (w : word Q d e), (u ≫* w↓)↓ = (u ≫* w)↓ := sorry

local infix ` ≫↓ `:50 := λ {c d e: V} (u : word Q c d) (w : word Q d e), (u ≫* w)↓ 


-- follows from the three lemmas above plus associativity of plain `append`
lemma word.append_reduce.assoc : Π {c d e f : V} (u : word Q c d) (w : word Q d e) (v : word Q e f), (u ≫↓ w) ≫↓ v = (u ≫↓ (w ≫↓ v)) := sorry

instance groupoid {w }

end free
end groupoid
end category_theory
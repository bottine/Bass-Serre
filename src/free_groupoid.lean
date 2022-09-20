import category_theory.path_category
import category_theory.quotient
import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv 
import data.set.lattice
import combinatorics.quiver.connected_component
import group_theory.subgroup.basic


open set
open classical function relation
local attribute [instance] prop_decidable


namespace category_theory
namespace groupoid
namespace free

universes u v 

variable {V : Type u}
variable (Q : quiver.{v+1} V)

inductive word : V → V → Sort*
| nil {c : V} : word c c
| cons_p {c d e : V} (p : Q.hom c d) (w : word d e) : word c e
| cons_n {c d e : V} (p : Q.hom d c) (w : word d e) : word c e

variable {Q}

def word.length : Π {c d : V}, word Q c d → ℕ
| _ _ word.nil := 0
| _ _ (word.cons_p _ t) := t.length.succ
| _ _ (word.cons_n _ t) := t.length.succ 

@[pattern]
def letter_p {c d : V} (p : Q.hom c d) : word Q c d := (word.cons_p p word.nil)
@[pattern]
def letter_n {c d : V} (p : Q.hom c d) : word Q d c := (word.cons_n p word.nil)

notation ` +[ ` p ` ] ` := letter_p p
notation ` -[ ` p ` ] ` := letter_n p

def word.append  : Π {c d e : V}, word Q c d → word Q d e → word Q c e
| _ _ _ (word.nil) w := w
| _ _ _ (word.cons_p p u) w := word.cons_p p (u.append w)
| _ _ _ (word.cons_n p u) w := word.cons_n p (u.append w)


@[simp] lemma word.nil_append {c d : V} {p : word Q c d} : word.nil.append p = p := sorry
@[simp] lemma word.append_nil {c d : V} {p : word Q c d} : p.append word.nil = p := sorry

@[simp] lemma word.append_assoc {c d e f : V} {p : word Q c d} {q : word Q d e} {r : word Q e f} : (p.append q).append r = p.append (q.append r) := sorry

infix ` ≫* `:100 := word.append

def word.reverse : Π {c d : V}, word Q c d → word Q d c
| _ _ (word.nil) := word.nil
| _ _ (word.cons_p p u) := (u.reverse.append (letter_n p))
| _ _ (word.cons_n p u) := (u.reverse.append (letter_p p))

def red_step {c d : V} (p : word Q c d) (q : word Q c d) : Prop :=
  (∃ (a b : V) (q₀ : word Q c a) (q₁ : word Q a d) (f : Q.hom a b), p = q₀ ≫* +[ f ] ≫* -[ f ] ≫* q₁ ∧ q = q₀ ≫* q₁)
∨ (∃ (a b : V) (q₀ : word Q c a) (q₁ : word Q a d) (f : Q.hom b a), p = q₀ ≫* -[ f ] ≫* +[ f ] ≫* q₁ ∧ q = q₀ ≫* q₁)

def free_groupoid (V : Type u) := V


@[simp]
lemma red_step.reverse  {c d : V} (p₀ p₁ : word Q c d) : red_step p₀.reverse p₁.reverse ↔ red_step p₀ p₁ := sorry 

@[simp]
lemma red_step.append_left_congr  {c d e : V} {p₀ p₁ : word Q c d} {q : word Q d e} : red_step p₀ p₁ → red_step (p₀ ≫* q) (p₁ ≫* q) :=
begin sorry end

@[simp]
lemma red_step.append_right_congr  {c d e : V} {p : word Q c d} {q₀ q₁ : word Q d e} :  red_step q₀ q₁ → red_step (p ≫* q₀) (p ≫* q₁) :=
begin sorry end


def quot_comp { c d e : V} (p : quot $ @red_step V Q c d) (q : quot $ @red_step V Q d e) : (quot $ @red_step V Q c e) :=
begin
  fapply quot.lift_on p,
  fapply quot.lift_on q,
  { rintro f g, exact quot.mk _ (g ≫* f),},
  { rintro f f' redf, apply funext, rintro g, apply quot.sound, apply red_step.append_right_congr redf, },
  { rintro f f' redf, apply quot.induction_on q, 
    { rintro, apply quot.sound, apply red_step.append_left_congr redf, }, },
end

def quot_comp' { c d e : V} (p : quot $ @red_step V Q c d) (q : quot $ @red_step V Q d e) : (quot $ @red_step V Q c e) :=
begin
  fapply quot.lift_on p,
  fapply quot.lift_on q,
  { rintro f g, exact quot.mk _ (g ≫* f),},
  { rintro f f' redf, apply funext, rintro g, apply quot.sound, apply red_step.append_right_congr redf, },
  { rintro f f' redf, apply quot.induction_on q, 
    rintro, apply quot.sound, apply red_step.append_left_congr redf, },
end

def quot_inv {c d : V} (p : quot $ @red_step V Q c d) : (quot $ @red_step V Q d c) :=
begin
  fapply quot.lift_on p,
  { rintro f, exact quot.mk _ (f.reverse), },
  { rintro f f' redf, apply quot.sound, simp only [red_step.reverse], exact redf, }
end

lemma id_quot_comp { c d : V} (p : quot $ @red_step V Q c d) : quot_comp (quot.mk _ (@word.nil V Q c)) p = p :=
begin
  apply quot.induction_on p,
  rintro, apply quot.eqv_gen_sound,
  simp only [word.nil_append],
  apply eqv_gen.refl,
end

lemma quot_comp_id { c d : V} (p : quot $ @red_step V Q c d) : quot_comp p (quot.mk _ (@word.nil V Q d)) = p :=
begin
  apply quot.induction_on p,
  rintro, apply quot.eqv_gen_sound,
  simp only [word.append_nil],
  apply eqv_gen.refl,
end

lemma quot_comp_assoc { c d e f : V} 
  (p : quot $ @red_step V Q c d) (q : quot $ @red_step V Q d e)  (r : quot $ @red_step V Q e f) :
  quot_comp (quot_comp p q) r = quot_comp p (quot_comp q r) :=
begin
  apply quot.induction_on p,
  apply quot.induction_on q,
  apply quot.induction_on r,
  rintro pp qq rr,
  dsimp only [quot_comp], simp only [quot.lift_on_mk, word.append_assoc],
end

lemma quot_inv_comp { c d : V} (p : quot $ @red_step V Q c d)  : quot_comp p (quot_inv p) = quot.mk _ (@word.nil V Q c) :=
begin
  apply quot.induction_on p,
  rintro,
  dsimp only [quot_comp, quot_inv], 
  simp only [quot.lift_on_mk], 
  apply quot.eqv_gen_sound,
  sorry,
end

lemma quot_comp_inv { c d : V} (p : quot $ @red_step V Q c d)  : quot_comp (quot_inv p) p = quot.mk _ (@word.nil V Q d) :=
begin
  apply quot.induction_on p,
  rintro,
  dsimp only [quot_comp, quot_inv], 
  simp only [quot.lift_on_mk], 
  apply quot.eqv_gen_sound,
  sorry,
end


def free_groupoid' : groupoid (free_groupoid V) :=
{ to_category :=
  { to_category_struct := 
    { to_quiver := 
      { hom := λ c d, quot (@red_step V Q c d) }
    , id := λ a, quot.mk _ (@word.nil V Q a)
    , comp := λ a b c p q, quot_comp p q }
  , id_comp' := λ a b p, id_quot_comp p
  , comp_id' := λ a b p, quot_comp_id p
  , assoc' := λ a b c d p q r, quot_comp_assoc p q r }
, inv := λ a b p, quot_inv p
, inv_comp' := λ a b p, (quot_comp_inv p)
, comp_inv' := λ a b p, quot_inv_comp p }


end free
end groupoid
end category_theory
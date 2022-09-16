import category_theory.path_category
import category_theory.quotient
import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv 
import data.set.lattice

/-
path_category == the free category of pats
quotient == quotienting morphisms by relations
algebra.hom.equiv to use ≃*
-/

open set

namespace category_theory
namespace groupoid

universes u v 

variables {C : Type u} 

instance group_at [groupoid C] (c : C): group (c ⟶ c) :=
{ mul := λ (x y : c ⟶ c), x ≫ y
, mul_assoc := category.assoc --λ (x y z : c ⟶ c), by simp only [category.assoc]
, one := 𝟙 c
, one_mul := category.id_comp
, mul_one := category.comp_id
, inv := groupoid.inv
, mul_left_inv := groupoid.inv_comp }

def group_at_hom [groupoid C] {c d : C} (f : c ⟶ d) : 
  (c ⟶ c) ≃* (d ⟶ d) := 
begin
  fsplit,
  exact λ γ, (groupoid.inv f) ≫ γ ≫ f,
  exact λ δ, f ≫ δ ≫ (groupoid.inv f),
  dsimp only [function.left_inverse], rintro x,
  simp only [category.assoc, groupoid.comp_inv, category.comp_id],
  rw [←category.assoc,groupoid.comp_inv,category.id_comp],
  dsimp only [function.right_inverse,function.left_inverse], rintro x,
  simp only [category.assoc, groupoid.comp_inv, 
             groupoid.inv_comp, category.comp_id],
  rw [←category.assoc,groupoid.inv_comp,category.id_comp],
  rintro x y,
  dsimp [has_mul.mul,mul_one_class.mul,monoid.mul,div_inv_monoid.mul,group.mul],
  have : x ≫ y = x ≫ f ≫ (groupoid.inv f) ≫ y, by 
  { congr, rw [←category.assoc,groupoid.comp_inv,category.id_comp], },
  rw this, 
  simp only [category.assoc],
end


def group_at_reachable [groupoid C] (c d : C)  (p : quiver.path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
begin
  induction p,
  { reflexivity },
  { apply p_ih.trans,  apply groupoid.group_at_hom, assumption, }
end




section subgroupoid

variable (G : groupoid C)
/-
structure subgroupoid :=
  (verts : set C)
  (arrws : ∀ {c : C} (hc : c ∈ verts) {d : C} (hd : d ∈ verts), set (G.hom c d))
  (inv' : ∀ {c : C} (hc : c ∈ verts) {d : C} (hd : d ∈ verts) {p : G.hom c d} (hp : p ∈ arrws hc hd), 
            groupoid.inv p ∈ arrws hd hc)
  (mul' : ∀ {c : C} (hc : c ∈ verts) {d : C} (hd : d ∈ verts) {e : C} (he : e ∈ verts)
            {p} (hp : p ∈ arrws hc hd) {q} (hq : q ∈ arrws hd he), 
            p ≫ q ∈ arrws hc he)

variable {G}

def is_subgroupoid (S T : subgroupoid G) : Prop :=
  ∃ hv : S.verts ⊆ T.verts, ∀ {c} (hc : c ∈ S.verts) {d} (hd : d ∈ S.verts),
    S.arrws hc hd ⊆ T.arrws (set.mem_of_mem_of_subset hc hv) (set.mem_of_mem_of_subset hd hv)

instance subgroupoid_le : has_le (subgroupoid G) := ⟨is_subgroupoid⟩

def top : subgroupoid G := ⟨set.univ, (λ _ _ _ _, set.univ), by {rintros,trivial,}, by {rintros, trivial,}⟩
def bot : subgroupoid G := ⟨∅, (λ _ _ _ _, ∅), by {rintros, simpa using hp,}, by {rintros, simpa using hp,}⟩

def le_top (S : subgroupoid G) : S ≤ top := 
begin
  dsimp only [top],
  fsplit; simp only [subset_univ, implies_true_iff],
end

def bot_le (S : subgroupoid G) : bot ≤ S :=
begin
  dsimp only [bot],
  fsplit; simp only [empty_subset, implies_true_iff],
end

def inter (S T : subgroupoid G) : subgroupoid G := 
begin
  refine_struct ⟨S.verts ∩ T.verts, λ c hc d hd, (S.arrws hc.1 hd.1)∩(T.arrws hc.2 hd.2),_,_⟩,
  { rintro c ⟨cS,cT⟩ d ⟨dS,dT⟩ p ⟨pS,pT⟩, exact ⟨S.inv' cS dS pS, T.inv' cT dT pT⟩ },
  { rintro c ⟨cS,cT⟩ d ⟨dS,dT⟩ e ⟨eS,eT⟩ p ⟨pS,pT⟩ q ⟨qS,qT⟩, exact ⟨S.mul' cS dS eS pS qS, T.mul' cT dT eT pT qT⟩,}
end

lemma le_inter {R S T : subgroupoid G} : R ≤ S → R ≤ T → R ≤ inter S T :=
begin
  rintros ⟨rsv,rsg⟩ ⟨rtv,rtg⟩, fsplit,
  use λ c cr, ⟨rsv cr,rtv cr⟩,
  rintro c cr d dr,
  rintro a ar, split, apply rsg, exact ar, apply rtg, exact ar,
end

def Inter (S : set (subgroupoid G)) : subgroupoid G := 
begin
  use set.Inter (λ s : S, s.val.verts),
  { rintro c hc d hd, 
    exact set.Inter (λ (s : S), s.val.arrws (by {apply hc, use s,} : c ∈ s.val.verts) (by {apply hd, use s,} : d ∈ s.val.verts)),},
  { rintro c hc d hd p hp, simp, rintro s sS, apply s.inv', apply hp, use s, use sS},
  { rintro c hc d hd e he p hp q hq, simp, rintro s sS, apply s.mul', apply hp, use s, use sS, apply hq, use s,},
end


instance : has_inf (subgroupoid G) := ⟨inter⟩

instance : complete_lattice (subgroupoid G) := sorry


-- Following Higgins
def generated (X : ∀ c d : C, set (G.hom c d)) : subgroupoid G := ⋂₀ { S : subgroupoid G | ∀ c d} 

-/

@[ext]
structure subgroupoid :=
  (arrws : ∀ (c d : C), set (G.hom c d))
  (inv' : ∀ {c d} {p : G.hom c d} (hp : p ∈ arrws c d), 
            groupoid.inv p ∈ arrws d c)
  (mul' : ∀ {c d e} {p} (hp : p ∈ arrws c d) {q} (hq : q ∈ arrws d e), 
            p ≫ q ∈ arrws c e)


variable {G}

def subgroupoid.carrier (S :subgroupoid G) : set C := {c : C | (S.arrws c c).nonempty }

def is_subgroupoid (S T : subgroupoid G) : Prop :=
  ∀ {c d}, S.arrws c d ⊆ T.arrws c d

instance subgroupoid_le : has_le (subgroupoid G) := ⟨is_subgroupoid⟩

def le_refl (S : subgroupoid G) : S ≤ S :=
by {rintro c d p, exact id,}

def le_trans (R S T : subgroupoid G) : R ≤ S → S ≤ T → R ≤ T :=
by {rintro RS ST c d, exact (@RS c d).trans (@ST c d), } 

def le_antisymm (R S : subgroupoid G) : R ≤ S → S ≤ R → R = S :=
by {rintro RS SR, ext c d p, exact ⟨(@RS c d p), (@SR c d p)⟩,}


instance : partial_order (subgroupoid G) := 
{ le := is_subgroupoid,
  le_refl := le_refl,
  le_trans := le_trans,
  le_antisymm := le_antisymm}

instance : has_top (subgroupoid G) := ⟨⟨(λ _ _, set.univ), by {rintros,trivial,}, by {rintros, trivial,}⟩⟩
instance : has_bot (subgroupoid G) := ⟨⟨(λ _ _, ∅), by {rintros, simpa using hp,}, by {rintros, simpa using hp,}⟩⟩

def le_top (S : subgroupoid G) : S ≤ ⊤  := 
begin
  dsimp only [has_top.top], 
  rintros c d,
  simp only [subset_univ], 
end

def bot_le (S : subgroupoid G) : ⊥   ≤ S :=
begin
  dsimp only [has_bot.bot],
  rintros c d,
  simp only [empty_subset, implies_true_iff],
end


instance : has_inf (subgroupoid G) := 
⟨ λ S T, 
  ⟨(λ c d, (S.arrws c d)∩(T.arrws c d))
  , by {rintros, exact ⟨S.inv' hp.1,T.inv' hp.2⟩}
  , by {rintros, exact ⟨S.mul' hp.1 hq.1, T.mul' hp.2 hq.2⟩}⟩⟩


lemma le_inf {R S T : subgroupoid G} : R ≤ S → R ≤ T → R ≤ S ⊓ T :=
begin
  rintros RS RT,
  rintros c d p pR, exact ⟨RS pR, RT pR⟩,
end

instance : has_Inf (subgroupoid G) :=
⟨ λ s,
  ⟨(λ c d, set.Inter (λ (S : s), S.val.arrws c d))
  , by {rintros, rw set.mem_Inter, rintro S, apply S.val.inv', apply hp, simp, use [S.val, S.prop], refl,}
  , by {rintros, rw set.mem_Inter, rintro S, apply S.val.mul', apply hp, use [S.val,S.prop], apply hq, use [S.val,S.prop],}⟩⟩




instance : complete_lattice (subgroupoid G) :=
{ bot          := (⊥),
  bot_le       := sorry,
  top          := (⊤),
  le_top       := sorry,
  inf          := (⊓),
  le_inf       := sorry,
  inf_le_left  := sorry,
  inf_le_right := sorry,
  .. complete_lattice_of_Inf (subgroupoid G) sorry }

-- Following Higgins, more or less
def generated (X : ∀ c d : C, set (G.hom c d)) : subgroupoid G := Inf { S : subgroupoid G | ∀ (c d : C), X c d ⊆ S.arrws c d }

inductive word  (X : ∀ c d : C, set (G.hom c d)) : C → C → Sort*
| nil {c : C} : word c c
| cons_p {c d e : C} (p : X c d) (w : word d e) : word c e
| cons_n {c d e : C} (p : X d c) (w : word d e) : word c e

def word.val {X : ∀ c d : C, set (G.hom c d)} : Π {c d : C}, word X c d → G.hom c d
| c .(c) (word.nil ) := (𝟙 c)
| _ _ (word.cons_p p w) := p.val ≫ w.val  
| _ _ (word.cons_n p w) := (G.inv p.val) ≫ w.val

def word.letter {X : ∀ c d : C, set (G.hom c d)} {c d : C} (p : X c d) : word X c d := (word.cons_p p word.nil)

@[pattern]
def word.letter_p {X : ∀ c d : C, set (G.hom c d)} {c d : C} (p : X c d) : word X c d := word.letter p
@[pattern]
def word.letter_n {X : ∀ c d : C, set (G.hom c d)} {c d : C} (p : X c d) : word X d c := (word.cons_n p word.nil)

def word.append  {X : ∀ c d : C, set (G.hom c d)} : Π {c d e : C}, word X c d → word X d e → word X c e
| _ _ _ (word.nil) w := w
| _ _ _ (word.cons_p p u) w := word.cons_p p (u.append w)
| _ _ _ (word.cons_n p u) w := word.cons_n p (u.append w)

def word.reverse {X : ∀ c d : C, set (G.hom c d)} : Π {c d : C}, word X c d → word X d c
| _ _ (word.nil) := word.nil
| _ _ (word.cons_p p u) := (u.reverse.append (word.letter_n p))
| _ _ (word.cons_n p u) := (u.reverse.append (word.letter_p p))

def word.nonempty  {X : ∀ c d : C, set (G.hom c d)} : Π {c d : C}, word X c d → Prop
| _ _ (word.nil) := false
| _ _ _ := true

lemma word.nonempty_reverse  {X : ∀ c d : C, set (G.hom c d)} {c d : C} (p : word X c d) : p.nonempty → p.reverse.nonempty := sorry
lemma word.nonempty_append  {X : ∀ c d : C, set (G.hom c d)} {c d e : C} (p : word X c d) (q : word X d e) :
  p.nonempty ∨ q.nonempty → (p.append q).nonempty := sorry

lemma word.letter_p_val {X : ∀ c d : C, set (G.hom c d)} {c d : C} (p : X c d) : (word.letter_p p).val = p.val := 
begin
  dsimp [word.letter_p,word.letter,word.val],
  simp only [category.comp_id],
end

lemma word.letter_n_val {X : ∀ c d : C, set (G.hom c d)} {c d : C} (p : X c d) : (word.letter_n p).val = G.inv p.val := 
begin
  dsimp [word.letter_n,word.val],
  simp only [category.comp_id],
end

lemma word.nonempty_letter_p {X : ∀ c d : C, set (G.hom c d)} {c d : C} (p : X c d) : (word.letter_p p).nonempty := trivial
lemma word.nonempty_letter_n {X : ∀ c d : C, set (G.hom c d)} {c d : C} (p : X c d) : (word.letter_n p).nonempty := trivial

lemma word.append_val (X : ∀ c d : C, set (G.hom c d)) {c d e : C} (u : word X c d) (w : word X d e) : 
  (u.append w).val = u.val ≫ w.val := sorry

lemma word.reverse_val (X : ∀ c d : C, set (G.hom c d)) {c d : C} (u : word X c d) : 
  (u.reverse).val = G.inv u.val := sorry


def generated' (X : ∀ c d : C, set (G.hom c d)) : subgroupoid G :=  
begin
  fsplit,
  {rintros c d, apply set.image (λ (p : word X c d), p.val ) {p : word X c d | p.nonempty},},
  {rintros c d _ ⟨u,un,rfl⟩, simp, use u.reverse, split, apply word.nonempty_reverse, apply un, apply word.reverse_val, },
  {rintros c d e _ ⟨u,un,rfl⟩ _ ⟨w,wn,rfl⟩, simp, use u.append w, split, apply word.nonempty_append, use or.inl un, apply word.append_val, },
end

lemma generated'_contains (X : ∀ c d : C, set (G.hom c d)) : ∀ (c d : C), X c d ⊆ (generated' X).arrws c d :=
begin
  rintros c d p pX,
  dsimp only [generated'],
  simp only [mem_image],
  let w : word X c d := word.letter_p ⟨p,pX⟩,
  use w, split, simp, exact word.letter_p_val ⟨p,pX⟩,
end

lemma contains_generated'  (X : ∀ c d : C, set (G.hom c d)) (S : subgroupoid G) (hS : ∀ (c d : C), X c d ⊆ S.arrws c d) :
  Π {c d : C} (p : word X c d) (pn : p.nonempty), p.val ∈ S.arrws c d
--| _ _ (word.nil) _ := by {}
| _ _ (word.letter_p p) _ := by {rw word.letter_p_val,apply hS, exact p.prop,}
| _ _ (word.letter_n p) _ := by {rw word.letter_n_val,apply S.inv',apply hS, exact p.prop,}
| _ _ (word.cons_p p (word.cons_p q u)) _ := by 
{ apply S.mul',
  { apply hS, exact p.prop, },
  { apply contains_generated', trivial,} }
| _ _ (word.cons_p p (word.cons_n q u)) _ := by
{ apply S.mul',
  { apply hS, exact p.prop, },
  { apply contains_generated', trivial,} }
| _ _ (word.cons_n p (word.cons_p q u)) _ := by
{ apply S.mul',
  { apply S.inv', apply hS, exact p.prop, },
  { apply contains_generated', trivial,} }
| _ _ (word.cons_n p (word.cons_n q u)) _ := by 
{ apply S.mul',
  { apply S.inv', apply hS, exact p.prop, },
  { apply contains_generated', trivial,} }

lemma generated_eq' (X : ∀ c d : C, set (G.hom c d)) : generated X = generated' X := 
begin
  apply le_antisymm,
  { have : ∀ (c d : C), X c d ⊆ (generated' X).arrws c d := generated'_contains X,
    exact @Inf_le _ _ { S : subgroupoid G | ∀ (c d : C), X c d ⊆ S.arrws c d } (generated' X) this,},
  { have : ∀ S : subgroupoid G, S ∈ { S : subgroupoid G | ∀ (c d : C), X c d ⊆ S.arrws c d} → (generated' X ) ≤ S, by
    { rintro S hS, rintro c d _ ⟨w,h,rfl⟩, simp only, apply contains_generated' X S hS w h,},
    apply @le_Inf _ _ { S : subgroupoid G | ∀ (c d : C), X c d ⊆ S.arrws c d } (generated' X) this, }
end


end subgroupoid


end groupoid
end category_theory
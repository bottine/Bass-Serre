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

def top : subgroupoid G := ⟨(λ _ _, set.univ), by {rintros,trivial,}, by {rintros, trivial,}⟩
def bot : subgroupoid G := ⟨(λ _ _, ∅), by {rintros, simpa using hp,}, by {rintros, simpa using hp,}⟩

def le_top (S : subgroupoid G) : S ≤ top := 
begin
  dsimp only [top], 
  rintros c d,
  simp only [subset_univ], 
end

def bot_le (S : subgroupoid G) : bot ≤ S :=
begin
  dsimp only [bot],
  rintros c d,
  simp only [empty_subset, implies_true_iff],
end

def le_refl (S : subgroupoid G) : S ≤ S :=
by {rintro c d p, exact id,}

def le_trans {R S T : subgroupoid G} : R ≤ S → S ≤ T → R ≤ T :=
by {rintro RS ST c d, exact (@RS c d).trans (@ST c d), } 

def le_antisymm {R S : subgroupoid G} : R ≤ S → S ≤ R → R = S :=
by {rintro RS SR, ext c d p, exact ⟨(@RS c d p), (@SR c d p)⟩,}

def inter (S T : subgroupoid G) : subgroupoid G := 
⟨(λ c d, (S.arrws c d)∩(T.arrws c d))
, by {rintros, exact ⟨S.inv' hp.1,T.inv' hp.2⟩}
, by {rintros, exact ⟨S.mul' hp.1 hq.1, T.mul' hp.2 hq.2⟩}⟩


lemma le_inter {R S T : subgroupoid G} : R ≤ S → R ≤ T → R ≤ inter S T :=
begin
  rintros RS RT,
  rintros c d p pR, exact ⟨RS pR, RT pR⟩,
end



instance : has_inf (subgroupoid G) := ⟨inter⟩

instance : complete_lattice (subgroupoid G) := sorry


-- Following Higgins
def generated (X : ∀ c d : C, set (G.hom c d)) : subgroupoid G := Inf { S : subgroupoid G | ∀ (c d : C), X c d ⊆ S.arrws c d }




inductive proper_word  (X : ∀ c d : C, set (G.hom c d)) : C → C → Sort*
| pos {c d : C} (p : X c d) : proper_word c d
| neg {c d : C} (p : X d c) : proper_word c d 
| cons_pos {c d e : C} (p : X c d) (w : proper_word d e) : proper_word c e
| cons_neg {c d e : C} (p : X d c) (w : proper_word d e) : proper_word c e

def proper_word.val {X : ∀ c d : C, set (G.hom c d)} : Π {c d : C}, proper_word X c d → G.hom c d
| _ _ (proper_word.pos p) := p
| _ _ (proper_word.neg p) := G.inv p
| _ _ (proper_word.cons_pos p w) := p.val ≫ w.val  
| _ _ (proper_word.cons_neg p w) := (G.inv p.val) ≫ w.val

def proper_word.append  {X : ∀ c d : C, set (G.hom c d)} : Π {c d e : C}, proper_word X c d → proper_word X d e → proper_word X c e
| _ _ _ (proper_word.pos p) w := proper_word.cons_pos p w 
| _ _ _ (proper_word.neg p) w := proper_word.cons_neg p w 
| _ _ _ (proper_word.cons_pos p u) w := proper_word.cons_pos p (u.append w)
| _ _ _ (proper_word.cons_neg p u) w := proper_word.cons_neg p (u.append w)

def proper_word.reverse {X : ∀ c d : C, set (G.hom c d)} : Π {c d : C}, proper_word X c d → proper_word X d c
| _ _ (proper_word.pos p) := proper_word.neg p 
| _ _ (proper_word.neg p) := proper_word.pos p  
| _ _ (proper_word.cons_pos p u) := (u.reverse.append (proper_word.neg p))
| _ _ (proper_word.cons_neg p u) := (u.reverse.append (proper_word.pos p))

def proper_word.append_val (X : ∀ c d : C, set (G.hom c d)) {c d e : C} (u : proper_word X c d) (w : proper_word X d e) : 
  (u.append w).val = u.val ≫ w.val := sorry

def proper_word.reverse_val (X : ∀ c d : C, set (G.hom c d)) {c d : C} (u : proper_word X c d) : 
  (u.reverse).val = G.inv u.val := sorry


def generated' (X : ∀ c d : C, set (G.hom c d)) : subgroupoid G :=  
begin
  fsplit,
  {rintros c d, apply set.range (λ (p : proper_word X c d), p.val ),},
  {rintros c d _ ⟨u,rfl⟩, simp, use u.reverse, apply proper_word.reverse_val, },
  {rintros c d e _ ⟨u,rfl⟩ _ ⟨w,rfl⟩, simp, use u.append w, apply proper_word.append_val, },
end

lemma generated'_contains (X : ∀ c d : C, set (G.hom c d)) : ∀ (c d : C), X c d ⊆ (generated' X).arrws c d :=
begin
  rintros c d p pX,
  dsimp only [generated'],
  simp only [mem_range],
  let w := @proper_word.pos C G X c d ⟨p,pX⟩,
  use w, refl,
end

lemma generated_eq' (X : ∀ c d : C, set (G.hom c d)) : generated X = generated' X := sorry


end subgroupoid


end groupoid
end category_theory
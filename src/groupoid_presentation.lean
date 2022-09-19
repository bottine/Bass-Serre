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

namespace category_theory

universes u v 

variables {C : Type u} 

instance groupoid.vertex_group [groupoid C] (c : C): group (c ⟶ c) :=
{ mul := λ (x y : c ⟶ c), x ≫ y
, mul_assoc := category.assoc --λ (x y z : c ⟶ c), by simp only [category.assoc]
, one := 𝟙 c
, one_mul := category.id_comp
, mul_one := category.comp_id
, inv := groupoid.inv
, mul_left_inv := groupoid.inv_comp }

@[simp] lemma groupoid.vertex_group.mul_eq_comp [groupoid C] (c : C) (γ δ : c ⟶ c) : γ * δ = γ ≫ δ := rfl
@[simp] lemma groupoid.vertex_group.inv_eq_inv [G : groupoid C] (c : C) (γ : c ⟶ c) : γ ⁻¹ = G.inv γ := rfl



def groupoid.vertex_group_isom_of_map [groupoid C] {c d : C} (f : c ⟶ d) : 
  (c ⟶ c) ≃* (d ⟶ d) := 
begin
  refine_struct ⟨λ γ, (groupoid.inv f) ≫ γ ≫ f, λ δ, f ≫ δ ≫ (groupoid.inv f), _, _, _⟩,
  { rintro x,
    simp_rw [category.assoc, groupoid.comp_inv, category.comp_id,←category.assoc, groupoid.comp_inv, category.id_comp], },
  { rintro x,
    simp_rw [category.assoc, groupoid.inv_comp, ←category.assoc, groupoid.inv_comp,category.id_comp, category.comp_id], },
  { rintro x y,
    have : x ≫ y = x ≫ f ≫ (groupoid.inv f) ≫ y, by 
    { congr, rw [←category.assoc,groupoid.comp_inv,category.id_comp], },
    simp [this,groupoid.vertex_group.mul_eq_comp,category.assoc], },
end


def groupoid.vertex_group_isom_of_path [groupoid C] (c d : C)  (p : quiver.path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
begin
  induction p,
  { reflexivity },
  { apply p_ih.trans,  apply groupoid.vertex_group_isom_of_map, assumption, }
end


@[simp]
lemma groupoid.inv_inv [G : groupoid C] (c d : C) [p : c ⟶ d] : G.inv (G.inv p) = p := 
  calc G.inv (G.inv p) = (G.inv (G.inv p)) ≫ (𝟙 d) : by rw category.comp_id
                  ... = (G.inv (G.inv p)) ≫ (G.inv p ≫ p) : by rw ←groupoid.inv_comp
                  ... = (G.inv (G.inv p) ≫ G.inv p) ≫ p : by rw ←category.assoc
                  ... = (𝟙 c) ≫ p : by rw groupoid.inv_comp
                  ... = p : by rw category.id_comp 


section
open quiver
instance [G : groupoid C] : has_reverse C := ⟨λ a b, G.inv⟩
end

namespace groupoid

section subgroupoid

variable (G : groupoid C)

@[ext]
structure subgroupoid :=
  (arrws : ∀ (c d : C), set (G.hom c d))
  (inv' : ∀ {c d} {p : G.hom c d} (hp : p ∈ arrws c d), 
            groupoid.inv p ∈ arrws d c)
  (mul' : ∀ {c d e} {p} (hp : p ∈ arrws c d) {q} (hq : q ∈ arrws d e), 
            p ≫ q ∈ arrws c e)

--instance: has_coe_to_fun (subgroupoid G) (λ S, Π (c d : C), set (G.hom c d)) := ⟨λ S, S.arrws⟩

variable {G}

lemma subgroupoid.nonempty_isotropy_to_mem_id (S :subgroupoid G) (c : C) : 
  (S.arrws c c).nonempty → 𝟙 c ∈ S.arrws c c :=
begin
  rintro ⟨γ,hγ⟩,
  have : 𝟙 c = γ * (G.inv γ), by simp only [vertex_group.mul_eq_comp, comp_inv],
  rw this, apply S.mul', exact hγ, apply S.inv', exact hγ,
end

def subgroupoid.carrier (S :subgroupoid G) : set C := {c : C | (S.arrws c c).nonempty }

def subgroupoid.as_wide_quiver  (S : subgroupoid G) : quiver C := ⟨λ c d, subtype $ S.arrws c d⟩


def subgroupoid.coe  (S : subgroupoid G) : groupoid (S.carrier) :=
{ to_category :=
  { to_category_struct := 
    { to_quiver := 
      { hom := λ a b, S.arrws a.val b.val }
    , id := λ a, ⟨𝟙 a.val, by {apply subgroupoid.nonempty_isotropy_to_mem_id, use a.prop,}⟩
    , comp := λ a b c p q, ⟨p.val ≫ q.val, S.mul' p.prop q.prop⟩, }
  , id_comp' := λ a b ⟨p,hp⟩, by simp only [category.id_comp]
  , comp_id' := λ a b ⟨p,hp⟩, by simp only [category.comp_id]
  , assoc' := λ a b c d ⟨p,hp⟩ ⟨q,hq⟩ ⟨r,hr⟩, by simp only [category.assoc] }
, inv := λ a b p, ⟨G.inv p.val, S.inv' p.prop⟩
, inv_comp' := λ a b ⟨p,hp⟩, by simp only [inv_comp]
, comp_inv' := λ a b ⟨p,hp⟩, by simp only [comp_inv] }

def subgroupoid.vertex_subgroup (S : subgroupoid G) (c : C) (hc : c ∈ S.carrier) : subgroup (c ⟶ c) :=
⟨ S.arrws c c 
, λ f g hf hg, S.mul' hf hg
, by {apply subgroupoid.nonempty_isotropy_to_mem_id, use hc,}
, λ f hf, S.inv' hf⟩


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

instance : has_inf (subgroupoid G) := 
⟨ λ S T, 
  ⟨(λ c d, (S.arrws c d)∩(T.arrws c d))
  , by {rintros, exact ⟨S.inv' hp.1,T.inv' hp.2⟩}
  , by {rintros, exact ⟨S.mul' hp.1 hq.1, T.mul' hp.2 hq.2⟩}⟩⟩

instance : has_Inf (subgroupoid G) :=
⟨ λ s,
  ⟨(λ c d, set.Inter (λ (S : s), S.val.arrws c d))
  , by {rintros, rw set.mem_Inter, rintro S, apply S.val.inv', apply hp, simp, use [S.val, S.prop], refl,}
  , by {rintros, rw set.mem_Inter, rintro S, apply S.val.mul', apply hp, use [S.val,S.prop], apply hq, use [S.val,S.prop],}⟩⟩

instance : complete_lattice (subgroupoid G) :=
{ bot          := (⊥),
  bot_le       := λ S c d, by {apply empty_subset,},
  top          := (⊤),
  le_top       := λ S c d, by {apply subset_univ,},
  inf          := (⊓),
  le_inf       := λ R S T RS RT c d p pR, ⟨RS pR, RT pR⟩,
  inf_le_left  := λ R S c d p pRS, pRS.left,
  inf_le_right := λ R S c d p pRS, pRS.right,
  .. complete_lattice_of_Inf (subgroupoid G) 
       ( by 
        { dsimp only [Inf], rintro s, constructor, 
          { rintro S Ss c d p hp, 
            simp only [Inter_coe_set, mem_Inter] at hp, 
            exact hp S Ss, },
          { rintro T Tl c d p pT, 
            simp only [Inter_coe_set, mem_Inter],
            rintros S Ss, apply Tl, exact Ss, exact pT,}}) }

def discrete [decidable_eq C] : subgroupoid G := 
⟨ λ c d, if h : c = d then {h.rec_on (G.id c)} else ∅
, by 
  { rintros c d p hp, 
    by_cases h : d = c, 
    { subst_vars, 
      simp only [eq_self_iff_true, congr_arg_mpr_hom_right, eq_to_hom_refl, category.comp_id, dite_eq_ite, if_true, mem_singleton_iff] at hp ⊢, 
      rw hp, apply inv_one, },
    { rw dif_neg (λ l : c = d, h l.symm) at hp, exact hp.elim, }, }
, by 
  { rintros c d e p hp q hq,
    by_cases h : d = c,
    { by_cases k : e = d; subst_vars,
      { simp only [eq_self_iff_true, dite_eq_ite, if_true, mem_singleton_iff] at ⊢ hp hq,
        rw [hp, hq], simp only [category.comp_id], }, 
      { simp only [eq_self_iff_true, dite_eq_ite, if_true, mem_singleton_iff] at ⊢ hp hq,
        rw dif_neg (λ l : d = e, k l.symm) at hq, exact hq.elim, }, },
    { rw dif_neg (λ l : c = d, h l.symm) at hp, exact hp.elim, }
  }⟩

structure is_normal (S : subgroupoid G) : Prop :=
  (wide : ∀ c, (𝟙 c) ∈ (S.arrws c c))  -- S is "wide": all vertices of G are covered
  (conj_mem : ∀ {c d} (p : c ⟶ d) (γ : c ⟶ c) (hs : γ ∈ S.arrws c c), ((G.inv p) ≫ γ ≫ p) ∈ (S.arrws d d))

def is_normal.conjugation_eq (S : subgroupoid G) (Sn : is_normal S) {c d} (p : c ⟶ d) : 
  set.bij_on (λ γ : c ⟶ c, (G.inv p) ≫ γ ≫ p) (S.arrws c c) (S.arrws d d) := 
begin
  split,
  { rintro γ γS, apply Sn.conj_mem, exact γS },
  split,
  { rintro γ₁ γ₁S γ₂ γ₂S h, 
    simp only at h,
    let h' := p ≫=(h =≫ (G.inv p)),--category_theory.eq_whisker h (G.inv p),
    simp only [category.assoc, comp_inv, category.comp_id] at h',
    simp only [←category.assoc, comp_inv, category.id_comp] at h', exact h', }, -- what's the quickest way here?
  { rintro δ δS, use (p ≫ δ ≫ (G.inv p)), split, 
    { have : p = G.inv (G.inv p), by {simp only [inv_inv],},
      nth_rewrite 0 this,
      apply Sn.conj_mem, exact δS, },
    { simp only [category.assoc, inv_comp, category.comp_id], 
      simp only [←category.assoc, inv_comp, category.id_comp], }}
end

lemma top_is_normal : is_normal (⊤ : subgroupoid G) := 
begin
  split,
  { rintro c, trivial },
  { rintro c d p γ hγ, trivial,}
end

lemma Inf_is_normal (s : set $ subgroupoid G) (sn : ∀ S ∈ s, is_normal S) : is_normal (Inf s) := 
begin
  split,
  { rintro c, dsimp only [Inf], rintro _ ⟨⟨S,Ss⟩,rfl⟩, exact (sn S Ss).wide c,},
  { rintros c d p γ hγ, dsimp only [Inf], rintro _ ⟨⟨S,Ss⟩,rfl⟩, apply (sn S Ss).conj_mem p γ, apply hγ, use ⟨S,Ss⟩,}
end 

lemma is_normal_vertex_subgroup (S : subgroupoid G) (Sn : is_normal S) (c : C) (cS : c ∈ S.carrier) : (S.vertex_subgroup c cS).normal :=
begin
  constructor,
  rintros x hx y, 
  simp only [vertex_group.mul_eq_comp, vertex_group.inv_eq_inv, category.assoc],
  have : y = G.inv (G.inv y), by {simp only [inv_inv],},
  nth_rewrite 0 this,
  apply Sn.conj_mem, exact hx,
end

/- Following Higgins -/
structure is_strict_normal (S : subgroupoid G) extends is_normal S : Prop := 
(discrete : ∀ (c d : C), c ≠ d →  (S.arrws c d) = ∅)

variable (X : ∀ c d : C, set (G.hom c d))



-- Following Higgins, more or less
def generated : subgroupoid G := Inf { S : subgroupoid G | ∀ (c d : C), X c d ⊆ S.arrws c d }


def set_as_quiver (X : ∀ c d : C, set (G.hom c d)) : quiver C := ⟨λ (c d : C), subtype $ X c d⟩

-- better this way?
def word'  (X : ∀ c d : C, set (G.hom c d)) : C → C → Sort* := 
@quiver.path _ (@quiver.symmetrify_quiver C (set_as_quiver X))

def word'.val (X : ∀ c d : C, set (G.hom c d)) {c d : C} (w : word' X c d) : c ⟶ d :=
begin
  induction w with a b u y z,
  { exact 𝟙 c, },
  { cases y, 
    { exact z ≫ y.val,},
    { exact z ≫ (G.inv y.val), }, },
end

inductive word  (X : ∀ c d : C, set (G.hom c d)) : C → C → Sort*
| nil {c : C} : word c c
| cons_p {c d e : C} (p : X c d) (w : word d e) : word c e
| cons_n {c d e : C} (p : X d c) (w : word d e) : word c e

variable {X}

def word.val  : Π {c d : C}, word X c d → G.hom c d
| c .(c) (word.nil ) := (𝟙 c)
| _ _ (word.cons_p p w) := p.val ≫ w.val  
| _ _ (word.cons_n p w) := (G.inv p.val) ≫ w.val

def word.letter {c d : C} (p : X c d) : word X c d := (word.cons_p p word.nil)

@[pattern]
def word.letter_p {c d : C} (p : X c d) : word X c d := word.letter p
@[pattern]
def word.letter_n {c d : C} (p : X c d) : word X d c := (word.cons_n p word.nil)

def word.append  : Π {c d e : C}, word X c d → word X d e → word X c e
| _ _ _ (word.nil) w := w
| _ _ _ (word.cons_p p u) w := word.cons_p p (u.append w)
| _ _ _ (word.cons_n p u) w := word.cons_n p (u.append w)

def word.reverse : Π {c d : C}, word X c d → word X d c
| _ _ (word.nil) := word.nil
| _ _ (word.cons_p p u) := (u.reverse.append (word.letter_n p))
| _ _ (word.cons_n p u) := (u.reverse.append (word.letter_p p))

def word.nonempty  : Π {c d : C}, word X c d → Prop
| _ _ (word.nil) := false
| _ _ _ := true

lemma word.nonempty_reverse  {c d : C} (p : word X c d) : p.nonempty → p.reverse.nonempty := sorry
lemma word.nonempty_append  {c d e : C} (p : word X c d) (q : word X d e) :
  p.nonempty ∨ q.nonempty → (p.append q).nonempty := sorry

lemma word.letter_p_val {c d : C} (p : X c d) : (word.letter_p p).val = p.val := 
begin
  dsimp [word.letter_p,word.letter,word.val],
  simp only [category.comp_id],
end

lemma word.letter_n_val {c d : C} (p : X c d) : (word.letter_n p).val = G.inv p.val := 
begin
  dsimp [word.letter_n,word.val],
  simp only [category.comp_id],
end

lemma word.nonempty_letter_p {c d : C} (p : X c d) : (word.letter_p p).nonempty := trivial
lemma word.nonempty_letter_n {c d : C} (p : X c d) : (word.letter_n p).nonempty := trivial

lemma word.append_val {c d e : C} (u : word X c d) (w : word X d e) : 
  (u.append w).val = u.val ≫ w.val := sorry

lemma word.reverse_val {c d : C} (u : word X c d) : 
  (u.reverse).val = G.inv u.val := sorry

variable (X)
include X
def generated' : subgroupoid G :=  
begin
  fsplit,
  {rintros c d, apply set.image (λ (p : word X c d), p.val ) {p : word X c d | p.nonempty},},
  {rintros c d _ ⟨u,un,rfl⟩, simp, use u.reverse, split, apply word.nonempty_reverse, apply un, apply word.reverse_val, },
  {rintros c d e _ ⟨u,un,rfl⟩ _ ⟨w,wn,rfl⟩, simp, use u.append w, split, apply word.nonempty_append, use or.inl un, apply word.append_val, },
end

lemma generated'_contains : ∀ (c d : C), X c d ⊆ (generated' X).arrws c d :=
begin
  rintros c d p pX,
  dsimp only [generated'],
  simp only [mem_image],
  let w : word X c d := word.letter_p ⟨p,pX⟩,
  use w, split, simp, exact word.letter_p_val ⟨p,pX⟩,
end

lemma contains_generated'  (S : subgroupoid G) (hS : ∀ (c d : C), X c d ⊆ S.arrws c d) :
  Π {c d : C} (p : word X c d) (pn : p.nonempty), p.val ∈ S.arrws c d
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

lemma generated_eq' : generated X = generated' X := 
begin
  apply le_antisymm,
  { have : ∀ (c d : C), X c d ⊆ (generated' X).arrws c d := generated'_contains X,
    exact @Inf_le _ _ { S : subgroupoid G | ∀ (c d : C), X c d ⊆ S.arrws c d } (generated' X) this,},
  { have : ∀ S : subgroupoid G, S ∈ { S : subgroupoid G | ∀ (c d : C), X c d ⊆ S.arrws c d} → (generated' X) ≤ S, by
    { rintro S hS, rintro c d _ ⟨w,h,rfl⟩, simp only, apply contains_generated' X S hS w h,},
    apply @le_Inf _ _ { S : subgroupoid G | ∀ (c d : C), X c d ⊆ S.arrws c d } (generated' X) this, }
end

def generated_on [decidable_eq C] (D : set C) : subgroupoid G := generated (λ c d, (X c d) ∪ (if h : c = d then by { rw h, exact {𝟙 d} } else ∅))


end subgroupoid


section strict_hom
/--
Higgins has his own version of normality and morphisms,  
where normality has a condition that all arrows between distinct vertices disappear, 
but I'm not sure this is the right way to look at it. 
We'll do it here, and try for a more general approach afterwards (where we don't have this added condition on normal subgroupoids, _and_ morphisms can play with vertices)
-/


variables {C} (G H : groupoid C) 



/- Following “Presentations of groupoids” by Higgins, p. 9, we call `strict_hom` the functors on underlying category being the identity on objects -/
structure strict_hom := 
( f   : Π {c d : C}, G.hom c d → H.hom c d) 
( one : Π (c : C), f (𝟙 c) = 𝟙 c )
( mul : Π {c d e : C} (p : G.hom c d) (q : G.hom d e), f (p ≫ q) = (f p) ≫ (f q ))
( inv : Π {c d : C} (p : G.hom c d), f (G.inv p) = (H.inv $ f p) )

infixr ` →** `:25 := strict_hom

def strict_im (φ : G →** H) : subgroupoid H := 
⟨ λ c d, {p : H.hom c d | ∃ q : G.hom c d, p = φ.f q}
, by {rintros c d _ ⟨q,rfl⟩, rw ← φ.inv, simp only [mem_set_of_eq, exists_apply_eq_apply'],}
, by {rintros c d e _ ⟨p,rfl⟩ _ ⟨q,rfl⟩, rw ← φ.mul, simp only [mem_set_of_eq, exists_apply_eq_apply'],}⟩ 


variables {G H}

def strict_ker [decidable_eq C] (φ : G →** H) : subgroupoid G := 
⟨ λ c d, if h : c = d then eq.rec_on h {f : c ⟶ c | φ.f f = 𝟙 c} else ∅
, by 
  { rintros c d p hp, 
    by_cases h : d = c, 
    { subst_vars, rw dif_pos (eq.refl d) at hp ⊢, simp only [mem_set_of_eq] at hp ⊢, rw φ.inv, rw hp, exact inv_one, },
    { rw dif_neg (λ l : c = d, h l.symm) at hp, finish, }}
, by 
  { rintros c d e p hp q hq, 
    by_cases h : d = c,
    { by_cases k : e = d,
      { subst_vars, rw dif_pos (eq.refl e) at hp hq ⊢, simp only [mem_set_of_eq] at hp hq ⊢, rw φ.mul, rw [hp,hq], exact mul_one (𝟙 e),},
      { subst_vars, rw dif_neg (λ l : d = e, k l.symm) at hq, finish,} },
    { rw dif_neg (λ l : c = d, h l.symm) at hp, finish, }}
⟩


--lemma normal_iff [decidable_eq C] (S : subgroupoid G) : is_strict_normal G S ↔ ∃ (H : groupoid C) (φ : G →** H), S = strict_ker φ := sorry


end strict_hom


section hom

variables (C) (D : Type*)
variables [G : groupoid C] [H : groupoid D]
variable [decidable_eq D]

def hom := @category_theory.functor C G.to_category D H.to_category
local infix `⥤i`:50 := hom

@[simp]
lemma functor.map_inv (φ : C ⥤i D) {c d : C} (f : c ⟶ d) :  
  φ.map (G.inv f) = H.inv (φ.map f) := 
calc φ.map (G.inv f) = (φ.map $ G.inv f) ≫ (𝟙 $ φ.obj c) : by rw [category.comp_id]
                 ... = (φ.map $ G.inv f) ≫ ((φ.map f) ≫ (H.inv $ φ.map f)) : by rw [comp_inv]
                 ... = ((φ.map $ G.inv f) ≫ (φ.map f)) ≫ (H.inv $ φ.map f) : by rw [category.assoc]
                 ... = (φ.map $ G.inv f ≫ f) ≫ (H.inv $ φ.map f) : by rw [functor.map_comp']
                 ... = (H.inv $ φ.map f) : by rw [inv_comp,functor.map_id,category.id_comp]            

def subgroupoid.map (φ : C ⥤i D) (φi : function.injective φ.obj) (S : subgroupoid G) : subgroupoid H :=
begin
  classical,
  fsplit,
  { rintros c d,
    by_cases h : (∃ a, φ.obj a = c) ∧ (∃ b, φ.obj b = d),
    { let a := h.left.some,
      let ac := h.left.some_spec,
      let b := h.right.some,
      let bd := h.right.some_spec,
      let := set.range (φ.map : (a ⟶ b) → ((φ.obj a) ⟶ (φ.obj b))),
      rw [ac,bd] at this, exact this, },
    { exact ∅, }, }, 
  { rintro c d p hp,
    by_cases h : (∃ a, φ.obj a = c) ∧ (∃ b, φ.obj b = d),
    { simp only at hp, 
      rw dif_pos h at hp, 
      simp only [eq_mp_eq_cast, cast_cast] at hp, 
      simp only [eq_mp_eq_cast, cast_cast], 
      rw dif_pos (and.intro h.right h.left), 
      sorry, },
    { simp only at hp, rw dif_neg h at hp, exact hp.elim,},},
  { sorry, }
end

def subgroupoid.comap {C D : Type*} [G : groupoid C] [H : groupoid D] (φ : C ⥤i D) (S : subgroupoid H) : subgroupoid G :=
⟨ λ c d, {f : c ⟶ d | φ.map f ∈ S.arrws (φ.obj c) (φ.obj d)}
, by 
  { rintros, simp only [mem_set_of_eq], rw functor.map_inv, apply S.inv', assumption, }
, by
  { rintros, simp only [mem_set_of_eq, functor.map_comp], apply S.mul'; assumption, }⟩

lemma subgroupoid.comap_mono {C D : Type*} [G : groupoid C] [H : groupoid D] (φ : C ⥤i D) (S T : subgroupoid H) : 
  S ≤ T → subgroupoid.comap φ S ≤ subgroupoid.comap φ T :=
begin
  rintro ST,
  dsimp only [subgroupoid.comap], 
  rintro c d p hp,
  exact ST hp, 
end

lemma is_normal.preimage [G: groupoid C] (φ : C ⥤i D) {S : subgroupoid H} (Sn : is_normal S) : is_normal (subgroupoid.comap φ S) :=
begin
  dsimp only [subgroupoid.comap],
  split,
  { rintro c, simp only [mem_set_of_eq, functor.map_id], apply Sn.wide, },
  { rintros c d f γ hγ, simp only [mem_set_of_eq, functor.map_comp, functor.map_inv], apply Sn.conj_mem, exact hγ, },
end

def ker [G : groupoid C] [H : groupoid D] (φ : C ⥤i D) : subgroupoid G := subgroupoid.comap φ (discrete) 

def mem_ker_iff  [G : groupoid C] [H : groupoid D] (φ : C ⥤i D) {c d : C} (f : c ⟶ d) : 
  f ∈ (ker C D φ).arrws c d ↔ ∃ (h : φ.obj c = φ.obj d), φ.map f = h.rec_on (𝟙 $ φ.obj c) :=
begin
  dsimp only [ker, discrete,subgroupoid.comap], 
  by_cases h : φ.obj c = φ.obj d,
  { simp only [dif_pos h, mem_singleton_iff, mem_set_of_eq], 
    split,
    { rintro e, use h, exact e, },
    { rintro ⟨_,e⟩, exact e, }},
  { simp only [dif_neg h, mem_empty_eq, set_of_false, false_iff, not_exists], 
    rintro e, exact (h e).elim, },
end

end hom


section quotient

def quot_v [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) := 
  (quot (λ (c d : C), (S.arrws c d).nonempty))


def quot_v.mk [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) (c : C) : quot_v S Sn:= 
  (quot.mk (λ (c d : C), (S.arrws c d).nonempty) c)


def conj  [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : 
  (Σ (a b : C), a ⟶ b) → (Σ (a b : C), a ⟶ b) → Prop := 
begin
  rintros ⟨a,b,f⟩ ⟨c,d,g⟩,
  exact ∃ (α ∈ S.arrws a c) (β ∈ S.arrws d b), f = α ≫ g ≫ β
end

@[refl]
lemma conj.refl [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : ∀ F, conj S Sn F F :=
begin
  rintro ⟨a,b,f⟩,
  use [(𝟙 a), Sn.wide a, (𝟙 b), Sn.wide b], 
  simp only [category.comp_id, category.id_comp],
end

@[symm]
lemma conj.symm [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : ∀ F G, conj S Sn F G → conj S Sn G F :=
begin
  rintros ⟨a,b,f⟩ ⟨c,d,g⟩ ⟨α,hα,β,hβ,rfl⟩,
  use [G.inv α, S.inv' hα, G.inv β, S.inv' hβ],
  simp only [category.assoc, comp_inv, category.comp_id], 
  rw ←category.assoc, 
  simp only [inv_comp, category.id_comp],
end

@[trans]
lemma conj.trans [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : 
  ∀ F G H, conj S Sn F G → conj S Sn G H → conj S Sn F H :=
begin
  rintros ⟨a₀,b₀,f₀⟩ ⟨a₁,b₁,f₁⟩ ⟨a₂,b₂,f₂⟩ ⟨α₀,hα₀,β₀,hβ₀,rfl⟩  ⟨α₁,hα₁,β₁,hβ₁,rfl⟩,
  use [α₀ ≫ α₁, S.mul' hα₀ hα₁, β₁ ≫ β₀, S.mul' hβ₁ hβ₀],
  simp only [category.assoc],
end

def quot_start [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : (quot $ conj S Sn) → (quot_v S Sn) :=
begin
  refine quot.lift _ _,
  { rintro ⟨a,b,f⟩, apply quot_v.mk, exact a,},
  { rintro ⟨a₀,b₀,f₀⟩ ⟨a₁,b₁,f₁⟩ ⟨α,hα,β,hβ,rfl⟩,simp,dsimp [quot_v.mk], apply quot.sound, exact ⟨α,hα⟩,}
end

def quot_end [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : (quot $ conj S Sn) → (quot_v S Sn) :=
begin
  refine quot.lift _ _,
  { rintro ⟨a,b,f⟩, apply quot_v.mk, exact b,},
  { rintro ⟨a₀,b₀,f₀⟩ ⟨a₁,b₁,f₁⟩ ⟨α,hα,β,hβ,rfl⟩,simp,dsimp [quot_v.mk], apply quot.sound, exact ⟨G.inv β,S.inv' hβ⟩,}
end

@[instance]
def quotient_quiver [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : 
  quiver (quot_v S Sn) := ⟨λc d, { F | quot_start S Sn F = c ∧ quot_end S Sn F = d }⟩

def quot_id'  [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : Π (c : quot_v S Sn),  (quot $ conj S Sn) :=
begin
  apply quot.lift, rotate,
  { rintro c, 
    exact quot.mk (conj S Sn) ⟨c,c,𝟙 c⟩ },
  { rintros c d ⟨f,fS⟩, 
    apply quot.sound, 
    use [f,fS,G.inv f, S.inv' fS],
    simp only [category.id_comp, comp_inv], }
end

def quot_id''  [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : Π (c : quot_v S Sn),  c ⟶ c :=
begin
  refine λ c, c.rec_on _ _, 
  { rintro c, dsimp only [quotient_quiver,quot_start,quot_end,quot_v.mk], 
    use quot.mk (conj S Sn) ⟨c,c,𝟙 c⟩, split, simp only, simp only, },
  { rintros c d ⟨f,fS⟩, 
    simp,
    have : quot.mk (λ (c d : C), (S.arrws c d).nonempty) c = quot.mk (λ (c d : C), (S.arrws c d).nonempty) d, by 
    { apply quot.sound, constructor, use fS,},
    simp, sorry
    }
end

def quotient_id  [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : Π (c : quot_v S Sn),  c ⟶ c :=
λ c, ⟨ quot_id' S Sn c, by {dsimp only [quot_id',quot_start,quot_end,quot_v.mk], induction c, simp, simp,}⟩

def quot_comp'  [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : Π (c d e : quot_v S Sn), (c ⟶ d) → (d ⟶ e) → (quot $ conj S Sn) :=
begin
  sorry
end


def quotient [G : groupoid C] (S : subgroupoid G) (Sn : is_normal S) : 
  groupoid (quot (λ (c d : C), (S.arrws c d).nonempty)) :=
{ to_category :=
  { to_category_struct := 
    { to_quiver := quotient_quiver S Sn 
    , id := quotient_id S Sn
    , comp := sorry }
  , id_comp' := sorry
  , comp_id' := sorry
  , assoc' := sorry }
, inv := sorry
, inv_comp' := sorry
, comp_inv' := sorry }


end quotient


end groupoid
end category_theory
import category_theory.path_category
import category_theory.quotient
import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv 


/-
path_category == the free category of pats
quotient == quotienting morphisms by relations
algebra.hom.equiv to use ≃*
-/


namespace category_theory

universes u v 

variables {C : Type u} [groupoid C]

instance groupoid.group_at (c : C) : group (c ⟶ c) :=
{ mul := λ (x y : c ⟶ c), x ≫ y
, mul_assoc := category.assoc --λ (x y z : c ⟶ c), by simp only [category.assoc]
, one := 𝟙 c
, one_mul := category.id_comp
, mul_one := category.comp_id
, inv := groupoid.inv
, mul_left_inv := groupoid.inv_comp }

def groupoid.group_at_hom {c d : C} (f : c ⟶ d) : 
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


def groupoid.group_at_reachable (c d : C)  (p : quiver.path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
begin
  induction p,
  { reflexivity },
  { apply p_ih.trans,  apply groupoid.group_at_hom, assumption, }
end


end category_theory
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

universes u v u' v'

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


@[simp] lemma word.nil_append {c d : V} {p : word Q c d} : word.nil.append p = p := rfl
@[simp] lemma word.append_nil {c d : V} {p : word Q c d} : p.append word.nil = p := by 
{ induction p, refl, all_goals { dsimp only [word.append], rw p_ih, }, }

@[simp] lemma word.append_assoc {c d e f : V} {p : word Q c d} {q : word Q d e} {r : word Q e f} : 
  (p.append q).append r = p.append (q.append r) := by
{ induction p, refl, all_goals { dsimp only [word.append], rw p_ih, }, }

infix ` ≫* `:100 := word.append

def word.reverse : Π {c d : V}, word Q c d → word Q d c
| _ _ (word.nil) := word.nil
| _ _ (word.cons_p p u) := (u.reverse.append (letter_n p))
| _ _ (word.cons_n p u) := (u.reverse.append (letter_p p))

lemma word.reverse_letter_p {c d : V} (p : Q.hom c d) : (letter_p p).reverse = letter_n p := by 
{ dsimp only [letter_p, letter_n, word.reverse], simp, }
lemma word.reverse_letter_n {c d : V} (p : Q.hom d c) : (letter_n p).reverse = letter_p p := by
{ dsimp only [letter_p, letter_n, word.reverse], simp, }

@[simp] lemma word.reverse_cons_p {c d e : V} (p : Q.hom c d) (w : word Q d e) : 
  (word.cons_p p w).reverse =  w.reverse.append (letter_n p) := rfl

@[simp] lemma word.reverse_cons_n {c d e : V} (p : Q.hom d c) (w : word Q d e) : 
  (word.cons_n p w).reverse =  w.reverse.append (letter_p p) := rfl

@[simp] lemma word.reverse_reverse  {c d : V} (w : word Q c d) : w.reverse.reverse = w := by
{ induction w, dsimp only [word.reverse], refl, sorry, sorry}
 
def red_step {c d : V} (p : word Q c d) (q : word Q c d) : Prop :=
  (∃ (a b : V) (q₀ : word Q c a) (q₁ : word Q a d) (f : Q.hom a b), p = q₀ ≫* +[ f ] ≫* -[ f ] ≫* q₁ ∧ q = q₀ ≫* q₁)
∨ (∃ (a b : V) (q₀ : word Q c a) (q₁ : word Q a d) (f : Q.hom b a), p = q₀ ≫* -[ f ] ≫* +[ f ] ≫* q₁ ∧ q = q₀ ≫* q₁)

@[simp]
lemma red_step.reverse  {c d : V} (p₀ p₁ : word Q c d) : red_step p₀.reverse p₁.reverse ↔ red_step p₀ p₁ :=
begin
  suffices : ∀ c d (p₀ p₁ : word Q c d),  red_step p₀ p₁ → red_step p₀.reverse p₁.reverse, 
  { split, rotate, exact this c d p₀ p₁,
    rintro h,
    rw  [←word.reverse_reverse p₀, ←word.reverse_reverse p₁],
    exact this d c _ _ h, },
  sorry
end

@[simp]
lemma red_step.append_left_congr  {c d e : V} {p₀ p₁ : word Q c d} {q : word Q d e} : red_step p₀ p₁ → red_step (p₀ ≫* q) (p₁ ≫* q) :=
begin sorry end

@[simp]
lemma red_step.append_right_congr  {c d e : V} {p : word Q c d} {q₀ q₁ : word Q d e} :  red_step q₀ q₁ → red_step (p ≫* q₀) (p ≫* q₁) :=
begin sorry end

def free_groupoid {V : Type u} (Q : quiver.{v+1} V) := V
def free_groupoid_quiver : quiver (free_groupoid Q) := { hom := λ c d, quot (@red_step V Q c d) }

def FQ  (Q : quiver.{v+1} V) := @free_groupoid_quiver V Q

def quot_comp { c d e : V} (p : (FQ Q).hom c d) (q : (FQ Q).hom d e) : (FQ Q).hom c e :=
quot.lift_on 
  p 
  (λ pp, quot.lift_on q 
    (λ qq, quot.mk _ (pp ≫* qq))
    (λ q₀ q₁ redq, quot.sound $ red_step.append_right_congr redq))
  (λ p₀ p₁ redp, quot.induction_on q $ λ qq, quot.sound $ red_step.append_left_congr redp)

def quot_id (c : V) := quot.mk (@red_step V Q c c) (word.nil)

def free_groupoid_category_struct : category_struct (free_groupoid Q)  := 
{ to_quiver := free_groupoid_quiver
, id := quot_id
, comp := λ a b c p q, quot_comp p q }
def FCS  (Q : quiver.{v+1} V) := @free_groupoid_category_struct V Q


lemma id_quot_comp { c d : V} (p : (FQ Q).hom c d) : quot_comp ((FCS Q).id c) p = p :=
quot.induction_on p $ λ pp, quot.eqv_gen_sound $ eqv_gen.refl pp

lemma quot_comp_id { c d : V} (p : (FQ Q).hom c d) : quot_comp p ((FCS Q).id d) = p :=
quot.induction_on p $ λ pp, quot.eqv_gen_sound $  by {simp, exact eqv_gen.refl pp}

lemma quot_comp_assoc { c d e f : V} 
  (p : (FQ Q).hom c d) (q : (FQ Q).hom d e)  (r : (FQ Q).hom e f) :
  quot_comp (quot_comp p q) r = quot_comp p (quot_comp q r) :=
quot.induction_on₃ p q r $ λ pp qq rr, by {dsimp [quot_comp], simp,}



def free_groupoid_category : category (free_groupoid Q)  := 
{ to_category_struct := free_groupoid_category_struct
  , id_comp' := λ a b p, id_quot_comp p
  , comp_id' := λ a b p, quot_comp_id p
  , assoc' := λ a b c d p q r, quot_comp_assoc p q r }
def FC  (Q : quiver.{v+1} V) := @free_groupoid_category V Q


def quot_inv {c d : V} (p : (FQ Q).hom c d) : (FQ Q).hom d c :=
quot.lift_on p
  (λ pp, quot.mk (@red_step V Q d c) pp.reverse)
  (λ p₀ p₁ redp , quot.sound $ by {simp only [red_step.reverse], exact redp })

lemma quot_inv_comp { c d : V} (p : (FQ Q).hom c d)  : quot_comp p (quot_inv p) = (FCS Q).id c :=
begin
  apply quot.induction_on p,
  rintro pp,
  dsimp only [quot_comp, quot_inv], 
  simp only [quot.lift_on_mk], 
  apply quot.eqv_gen_sound,
  induction pp with _ two thr fou fiv six sev eig nin ten,
  { exact eqv_gen.refl _, },
  { apply eqv_gen.trans ((word.cons_p fiv six) ≫* (word.cons_p fiv six).reverse) (six ≫* six.reverse) (word.nil), },
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

@[simp]
lemma quot_cons_p { c d e : V} (f : Q.hom c d) (w : word Q d e) : quot.mk red_step (word.cons_p f w) = (FCS Q).comp (quot.mk red_step +[ f ]) (quot.mk red_step w) := sorry
@[simp]
lemma quot_cons_n { c d e : V} (f : Q.hom d c) (w : word Q d e) : quot.mk red_step (word.cons_n f w) = (FCS Q).comp (quot.mk red_step $ letter_n f) (quot.mk red_step w) := sorry



instance : groupoid (free_groupoid Q) :=
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

def ι : prefunctor V (free_groupoid Q) := 
{ obj := λ x, x 
, map := λ x y p, quot.mk _ (letter_p p)}

def lift_word {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : Π {x y : V} (w : word Q x y), (φ.obj x) ⟶ (φ.obj y)
| x _ (word.nil) := 𝟙 (φ.obj x)
| x z (@word.cons_p _ _ _ y _ p w) := G'.comp (φ.map p) (lift_word w)
| x z (@word.cons_n _ _ _ y _ p w) := G'.comp (G'.inv $ φ.map p) (lift_word w)

@[simp]
lemma lift_word_append  {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : Π {x y z : V} (u : word Q x y) (w : word Q y z),
   lift_word φ (u ≫* w) = (lift_word φ u) ≫ (lift_word φ w) := sorry

@[simp]
lemma lift_word_reverse  {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : Π {x y : V} (u : word Q x y) ,
   lift_word φ (u.reverse) = G'.inv (lift_word φ u) := sorry

@[simp]
lemma lift_word_nil  {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : Π (x : V),  (lift_word φ (word.nil : word Q x x)) = 𝟙 (φ.obj x) :=
by { rintro x, dsimp only [lift_word], refl, }


@[simp]
lemma lift_word_letter_p  {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : Π (x y : V) (u : Q.hom x y),  (lift_word φ (letter_p u : word Q x y)) = φ.map u :=
by { rintro x y p, dsimp [lift_word, letter_p, lift_word_nil], simp, }

@[simp]
lemma lift_word_letter_n  {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : Π (x y : V) (u : Q.hom y x),  (lift_word φ (letter_n u : word Q x y)) = G'.inv (φ.map u) :=
by { rintro x y p, dsimp [lift_word, letter_n, lift_word_nil], simp, }


def lift_word_congr {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : Π {x y : V} (w₀ w₁ : word Q x y) (redw : red_step w₀ w₁), lift_word φ w₀ = lift_word φ w₁ :=
begin
  rintros x y w₀ w₁ redw,
  rcases redw with (⟨u,v,r₀,r₁,p,rfl,rfl⟩|⟨u,v,r₀,r₁,p,rfl,rfl⟩),
  { rw [←word.reverse_letter_p p],
    simp only [word.append_assoc, lift_word_append, lift_word_reverse],
    nth_rewrite_lhs 1 ←category.assoc, 
    rw groupoid.comp_inv, simp only [category.id_comp], },
  { rw [←word.reverse_letter_n p],
    simp only [word.append_assoc, lift_word_append, lift_word_reverse],
    nth_rewrite_lhs 1 ←category.assoc, 
    rw groupoid.comp_inv, simp only [category.id_comp], },
end

def lift {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : free_groupoid Q ⥤ V' :=
{ obj := φ.obj
, map := λ x y, quot.lift (λ p, lift_word φ p) (λ p₀ p₁ (redp : red_step p₀ p₁), lift_word_congr φ p₀ p₁ redp)
, map_id' := λ x, by { dsimp only [lift_word,category_struct.id], refl,  }
, map_comp' := λ x y z f g, by { refine quot.induction_on₂ f g _, rintro ff gg, dsimp only [lift_word,category_struct.comp,quot_comp],simp only [lift_word_append],  } }


--mathlib (stolen from functor.ext)
lemma _root_.category_theory.functor.ext' {C D : Type*} [category C] [category D] {F G : C ⥤ D} 
  (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ (X Y : C) (f : X ⟶ Y), F.map f = by {rw [h_obj X, h_obj Y], exact G.map f}) :
  F = G :=
begin
  cases F with F_obj _ _ _, cases G with G_obj _ _ _,
  obtain rfl : F_obj = G_obj, by { ext X, apply h_obj },
  congr,
  funext X Y f,
  simpa using h_map X Y f
end


--mathlib (stolen from functor.ext), 
@[ext] lemma ext {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [Q' : quiver.{v'+1} V'] {F G : prefunctor V V'} 
  (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ (X Y : V) (f : X ⟶ Y), F.map f = by {rw [h_obj X, h_obj Y], exact G.map f}) : F = G :=
begin
  cases F with F_obj _, cases G with G_obj _,
  obtain rfl : F_obj = G_obj, by { ext X, apply h_obj },
  congr,
  funext X Y f,
  simpa using h_map X Y f,
end

lemma lift_spec {V : Type u} [Q : quiver.{v+1} V] {V' : Type u'} [G' : groupoid V']
  (φ : prefunctor V V') : ι.comp (lift φ).to_prefunctor = φ :=
begin
  ext, rotate,
  rcases φ with ⟨φo,φm⟩,
  { rintro x, dsimp only, refl, },
  { subst_vars, apply lift_word_letter_p, },
end

@[simp]
lemma _root_.category_theory.functor.groupoid_map_inv  {C D : Type*} [G : groupoid C] [H : groupoid D] (φ : C ⥤ D)
  {c d : C} (f : c ⟶ d) :  
  φ.map (G.inv f) = H.inv (φ.map f) := 
calc φ.map (G.inv f) = (φ.map $ G.inv f) ≫ (𝟙 $ φ.obj c) : by rw [category.comp_id]
                 ... = (φ.map $ G.inv f) ≫ ((φ.map f) ≫ (H.inv $ φ.map f)) : by rw [comp_inv]
                 ... = ((φ.map $ G.inv f) ≫ (φ.map f)) ≫ (H.inv $ φ.map f) : by rw [category.assoc]
                 ... = (φ.map $ G.inv f ≫ f) ≫ (H.inv $ φ.map f) : by rw [functor.map_comp']
                 ... = (H.inv $ φ.map f) : by rw [inv_comp,functor.map_id,category.id_comp]            


lemma lift_unique  (V : Type u) [Q : quiver.{v+1} V] (V' : Type u') [G' : groupoid V']
  (φ : prefunctor V V') (Φ : free_groupoid Q ⥤ V') : (ι.comp Φ.to_prefunctor) = φ → Φ = (lift φ) :=
begin
  rintro h, subst h,
  fapply functor.ext',
  { rintro x, dsimp [lift,ι], refl, },
  { rintro X Y f, 
    simp only [eq_mpr_eq_cast, cast_eq],
    refine quot.induction_on f _,
    refine word.rec _ _ _,
    { rintro x, convert functor.map_id Φ x, },
    { rintro x y z p w IHw, 
      rw [quot_cons_p, functor.map_comp, IHw],
      congr, }, 
    { rintro x y z p w IHw, 
      rw [quot_cons_n, functor.map_comp, IHw, functor.map_comp], apply congr_arg2,
      { dsimp [lift,ι], rw lift_word_letter_n, rw ←word.reverse_letter_p, simp only [prefunctor.comp_map], 
        convert functor.groupoid_map_inv Φ (quot.mk red_step  +[ p ]) , },
      refl, }, 
            
  },

end

end free
end groupoid
end category_theory
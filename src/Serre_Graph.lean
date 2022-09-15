import combinatorics.quiver.basic
import algebra.group.basic
import algebra.hom.group


universes u v w

/-
Random thoughts:

* A graph *à la Serre* with choice of orientation is really just a quiver, so we might as well work
  with quivers?
* A quiver has a freely generated associated groupoid: 

  Quiver I -----> SerreGraph I
      \           /
       \         /
        \       /
         v     v
        Groupoid I

then what?


-/


class Serre (obj : Type u)
extends quiver.{v+1} obj : Type (max u (v+1)) :=
(ι       : Π X Y : obj, (X ⟶ Y) → (Y ⟶ X))
(ι_inv   : Π {X Y : obj} (e : X ⟶ Y), @ι Y X (@ι X Y e) = e)
(ι_nofix : Π {X : obj} (e : X ⟶ X), @ι X X e ≠ e)

def disorient {obj : Type u} (q : quiver.{v+1} obj) : quiver.{v+1} obj := ⟨λ X Y, (q.hom X Y) ⊕ (q.hom Y X)⟩

def disorient_ι {obj : Type u} (q : quiver.{v+1} obj) : ∀ {X Y}, (disorient q).hom X Y → (disorient q).hom Y X
| _ _ (sum.inl e) := sum.inr e 
| _ _ (sum.inr e) := sum.inl e

lemma disorient_ι_nofix {obj : Type u} (q : quiver.{v+1} obj) : 
  ∀ {X} (e : (disorient q).hom X X), (disorient_ι q) e ≠ e
| _ (sum.inl e) := λ eq, sum.no_confusion eq
| _ (sum.inr e) := λ eq, sum.no_confusion eq 

lemma disorient_ι_inv {obj : Type u} (q : quiver.{v+1} obj) : 
  ∀ {X Y} (e : (disorient q).hom X Y), (disorient_ι q) ((disorient_ι q) e) = e 
| _ _ (sum.inl e) := rfl
| _ _ (sum.inr e) := rfl 


class GoG' (obj : Type u) extends quiver.{v+1} obj := 
  (vertex_carrier : Π X : obj, Type w)
  (edge_carrier : Π {X Y : obj} (e : X ⟶ Y), Type w)
  (vertex_group : Π X : obj, group (vertex_carrier X))
  (edge_group : Π {X Y : obj} (e : X ⟶ Y), group (edge_carrier e))
  (edge_start : Π {X Y : obj} (e : X ⟶ Y), edge_carrier e →* vertex_carrier X)
  (edge_start_inj : Π {X Y : obj} (e : X ⟶ Y), function.injective (edge_start e))
  (edge_end   : Π {X Y : obj} (e : X ⟶ Y), edge_carrier e →* vertex_carrier X)
  (edge_end_inj : Π {X Y : obj} (e : X ⟶ Y), function.injective (edge_end e))

class GoG (obj : Type u)
extends Serre obj :=
(vertex_carrier : Π X : obj, Type w)
(edge_carrier : Π {X Y : obj} (e : X ⟶ Y), Type w)
(vertex_group : Π X : obj, group (vertex_carrier X))
(edge_group : Π {X Y : obj} (e : X ⟶ Y), group (edge_carrier e))
(edge_start : Π {X Y : obj} (e : X ⟶ Y), edge_carrier e →* vertex_carrier X)
(edge_start_inj : Π {X Y : obj} (e : X ⟶ Y), function.injective (edge_start e))
(edge_ι : Π {X Y : obj} (e : X ⟶ Y), edge_carrier e →* edge_carrier (@ι X Y e))
(edge_ι_inv : Π {X Y : obj} (e : X ⟶ Y), by { let lol := ((edge_ι _).comp (edge_ι e)), 
                                               have eee := ι_inv e, convert lol, } = @id (edge_carrier e)) -- doesn't work


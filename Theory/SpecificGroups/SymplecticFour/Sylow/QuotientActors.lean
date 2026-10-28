module

public import Theory.SpecificGroups.SymplecticFour.Sylow.QuotientActors.Actors
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Faithful central-quotient actors on a symplectic Sylow group

The literal unipotent group has quotient by its center equal to the additive
plane with coordinates `(b,v)`. The two central coordinates identify its
square map with `(b²v,bv)`. Every group automorphism therefore induces the
compatible plane and center automorphisms classified in `Quadratic`.

For field degree greater than two, a two-group acting faithfully on this
central quotient is cyclic. This supplies the intrinsic Sylow-action step
of the noncentral branch of Aschbacher–Smith, 2.4.24, without selecting an
ambient Lie-type component or extending the actors to the symplectic group.
-/

@[expose] public section

noncomputable section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.QuotientActors
open CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

abbrev SylowGroup (F : Type*) [Field F] := ↥(unipotent (F:=F))

def planeProjection : SylowGroup F →* Multiplicative (F × F) where
  toFun g := Multiplicative.ofAdd
    (g.val.val (.inl 0) (.inl 1),g.val.val (.inl 1) (.inr 1))
  map_one' := by
    change Multiplicative.ofAdd ((1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (.inl 0) (.inl 1),
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (.inl 1) (.inr 1))=1
    simp
  map_mul' g h := by
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
    obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective h
    change Multiplicative.ofAdd ((element b u w v*element c z t a).val.val (.inl 0) (.inl 1),
      (element b u w v*element c z t a).val.val (.inl 1) (.inr 1))=_
    rw [element_mul,element_matrix,element_matrix,element_matrix]
    rfl

lemma planeProjection_element (b u w v : F) :
    planeProjection (element b u w v)=Multiplicative.ofAdd (b,v) := by
  change Multiplicative.ofAdd ((element b u w v).val.val (.inl 0) (.inl 1),
    (element b u w v).val.val (.inl 1) (.inr 1))=_
  rw [element_matrix]
  rfl

lemma planeProjection_surjective : Function.Surjective (planeProjection (F:=F)) := by
  intro x
  exact ⟨element x.toAdd.1 0 0 x.toAdd.2,planeProjection_element _ _ _ _⟩

lemma planeProjection_ker : (planeProjection (F:=F)).ker=center (SylowGroup F) := by
  ext g
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective g
  rw [MonoidHom.mem_ker,planeProjection_element,mem_center_iff_coordinates]
  change (b,v)=(0,0) ↔ b=0 ∧ v=0
  simp only [Prod.mk.injEq]

def planeQuotient : (SylowGroup F ⧸ center (SylowGroup F)) →* Multiplicative (F × F) :=
  QuotientGroup.lift (center (SylowGroup F)) planeProjection (le_of_eq planeProjection_ker.symm)

lemma planeQuotient_bijective : Function.Bijective (planeQuotient (F:=F)) := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (center (SylowGroup F)) x
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [←planeProjection_ker]
    exact hx
  · intro x
    obtain ⟨g,hg⟩ := planeProjection_surjective x
    exact ⟨QuotientGroup.mk' (center (SylowGroup F)) g,hg⟩

def planeCoordinatesEquiv : (SylowGroup F ⧸ center (SylowGroup F)) ≃* Multiplicative (F × F) :=
  MulEquiv.ofBijective planeQuotient planeQuotient_bijective

lemma planeCoordinatesEquiv_mk (g : SylowGroup F) :
    planeCoordinatesEquiv (QuotientGroup.mk' (center (SylowGroup F)) g)=planeProjection g := rfl

def centralEquiv : Multiplicative (F × F) ≃* center (SylowGroup F) :=
  (MulEquiv.prodMultiplicative F F).trans centerEquiv

lemma centralEquiv_val (x : F × F) :
    (centralEquiv (Multiplicative.ofAdd x)).val=theta x.1 x.2 := rfl

def planeAction : MulAut (SylowGroup F) →* MulAut (Multiplicative (F × F)) :=
  (MulAut.congr planeCoordinatesEquiv).toMonoidHom.comp (quotientAut (center (SylowGroup F)))

def centralAction (a : MulAut (SylowGroup F)) : (F × F) ≃+ (F × F) :=
  (MulAut.congr centralEquiv.symm (MulAut.characteristic (center (SylowGroup F)) a)).toAdditive

lemma planeAction_apply (a : MulAut (SylowGroup F)) (g : SylowGroup F) :
    planeAction a (planeProjection g)=planeProjection (a g) := by
  rw [←planeCoordinatesEquiv_mk,←planeCoordinatesEquiv_mk]
  change planeCoordinatesEquiv (quotientAut (center (SylowGroup F)) a
    (planeCoordinatesEquiv.symm (planeCoordinatesEquiv (QuotientGroup.mk' (center (SylowGroup F)) g))))=_
  rw [MulEquiv.symm_apply_apply,quotientAut_apply_mk]

lemma centralAction_apply (a : MulAut (SylowGroup F)) (x : F × F) :
    (centralEquiv (Multiplicative.ofAdd (centralAction a x))).val=
      a (centralEquiv (Multiplicative.ofAdd x)).val := by
  change (centralEquiv (centralEquiv.symm
    (MulAut.characteristic (center (SylowGroup F)) a (centralEquiv (Multiplicative.ofAdd x))))).val=_
  rw [MulEquiv.apply_symm_apply]
  rfl

lemma square_compatibility (a : MulAut (SylowGroup F)) (x : F × F) :
    squareMap ((planeAction a (Multiplicative.ofAdd x)).toAdd)=
      centralAction a (squareMap x) := by
  let g := element x.1 0 0 x.2
  have hp : planeProjection g=Multiplicative.ofAdd x := planeProjection_element _ _ _ _
  rw [←hp,planeAction_apply]
  obtain ⟨⟨b,u,w,v⟩,hg⟩ := element_surjective (a g)
  rw [←hg,planeProjection_element]
  apply_fun (fun y : F × F => (centralEquiv (Multiplicative.ofAdd y)).val)
    using Subtype.val_injective.comp centralEquiv.injective
  change (centralEquiv (Multiplicative.ofAdd (squareMap (b,v)))).val=
    (centralEquiv (Multiplicative.ofAdd (centralAction a (squareMap x)))).val
  rw [centralAction_apply,centralEquiv_val,centralEquiv_val]
  change theta (b^2*v) (b*v)=a (theta (x.1^2*x.2) (x.1*x.2))
  rw [←element_square b u w v,←element_square x.1 0 0 x.2]
  change (element b u w v)^2=a (g^2)
  change element b u w v=a g at hg
  rw [hg,map_pow]

lemma isCyclic_of_faithful_unipotent_centerQuotient {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 2<n)
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup 2 A)
    (α : A →* MulAut (unipotent (F:=F)))
    (hfaithful : Function.Injective (((center (unipotent (F:=F))).quotientAut).comp α)) :
    IsCyclic A := by
  let ρ := (planeAction (F:=F)).comp α
  have hi : Function.Injective ρ := by
    intro a b hab
    apply hfaithful
    apply (MulAut.congr (planeCoordinatesEquiv (F:=F))).injective
    exact hab
  apply isCyclic_of_faithful_quadratic_action hF hn hA ρ hi
  intro a
  exact ⟨centralAction (α a),square_compatibility (α a)⟩

end Theory.SpecificGroups.SymplecticFour.QuotientActors

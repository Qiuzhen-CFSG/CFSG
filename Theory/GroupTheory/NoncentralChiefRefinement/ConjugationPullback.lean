module
public import Theory.GroupTheory.NoncentralChiefRefinement.BinaryFlagSections
public import Theory.Representation.Quotient

/-!
# Chief sections pulled back through a surjective actor map

Let q : K → J be surjective and R normal in J. Equivariant additive binary
coordinates on R induce one-copy coordinates on q⁻¹(R)/ker(q), using the
literal relative quotient and conjugation action. If the action on those
coordinates is irreducible and nontrivial, this is one noncentral two-chief
factor. The proof uses the first isomorphism theorem and inflation of
irreducibility, without a presumed chief interval or factor count.

The marked Borel core in Aschbacher–Smith 14.7.70 (printed p.1074/PDF p.1091)
is a consumer; the construction here is independent of that source setup.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace NoncentralChiefRefinement.ConjugationPullback
variable {K J M : Type*} [Group K] [Group J] [AddCommGroup M] [Module (ZMod 2) M]
  (q : K →* J) (R : NormalNode J) (ρ : Representation (ZMod 2) J M)

def kernelNode : NormalNode K := ⟨q.ker, show q.ker.Normal from inferInstance⟩

def preimageNode : NormalNode K :=
  ⟨R.val.comap q, show (R.val.comap q).Normal from inferInstance⟩

theorem kernel_le_preimage : kernelNode q ≤ preimageNode q R := by
  intro k hk
  change q k ∈ R.val
  rw [show q k = 1 from hk]
  exact R.val.one_mem

def toSubgroup : (preimageNode q R).val →* R.val where
  toFun x := ⟨q x.val, x.property⟩
  map_one' := Subtype.ext q.map_one
  map_mul' x y := Subtype.ext (q.map_mul x.val y.val)

theorem toSubgroup_surjective (hq : Function.Surjective q) :
    Function.Surjective (toSubgroup q R) := by
  intro r
  obtain ⟨k, hk⟩ := hq r.val
  refine ⟨⟨k, ?_⟩, Subtype.ext hk⟩
  change q k ∈ R.val
  rw [hk]
  exact r.property

variable (e : R.val ≃* Multiplicative M)
  (he : ∀ (j : J) (r : R.val),
    (e (MulAut.conjNormal j r)).toAdd = ρ j (e r).toAdd)

def coordinateMap : BinaryFlag.Map (preimageNode q R) (ρ.comp q) where
  hom := e.toMonoidHom.comp (toSubgroup q R)
  equivariant k x := by
    change (e (toSubgroup q R (MulAut.conjNormal k x))).toAdd = _
    rw [show toSubgroup q R (MulAut.conjNormal k x) =
      MulAut.conjNormal (q k) (toSubgroup q R x) by
        apply Subtype.ext
        change q (k * x.val * k⁻¹) = q k * q x.val * (q k)⁻¹
        rw [q.map_mul, q.map_mul, q.map_inv]]
    exact he (q k) (toSubgroup q R x)

theorem coordinateMap_surjective (hq : Function.Surjective q) :
    Function.Surjective (coordinateMap q R ρ e he).hom :=
  e.surjective.comp (toSubgroup_surjective q R hq)

theorem coordinateMap_kernel :
    (coordinateMap q R ρ e he).hom.ker =
      (kernelNode q).val.subgroupOf (preimageNode q R).val := by
  ext x
  change e (toSubgroup q R x) = 1 ↔ q x.val = 1
  rw [e.map_eq_one_iff]
  exact Subtype.ext_iff

def coordinates (hq : Function.Surjective q) :
    SectionCoordinates (kernelNode q) (preimageNode q R) (ρ.comp q) 1 :=
  (coordinateMap q R ρ e he).coordinates
    (coordinateMap_surjective q R ρ e he hq) (coordinateMap_kernel q R ρ e he)

theorem noncentral (hq : Function.Surjective q) (hρ : ∃ j v, ρ j v ≠ v) :
    ∃ k v, (ρ.comp q) k v ≠ v := by
  obtain ⟨j, v, hv⟩ := hρ
  obtain ⟨k, rfl⟩ := hq j
  exact ⟨k, v, hv⟩

include e he in
theorem covBy (hq : Function.Surjective q) [Representation.IsIrreducible ρ]
    (hρ : ∃ j v, ρ j v ≠ v) : kernelNode q ⋖ preimageNode q R := by
  let := (Representation.irreducible_comp_surjective_iff q hq ρ).mpr inferInstance
  exact (coordinates q R ρ e he hq).covBy (kernel_le_preimage q R) (noncentral q ρ hq hρ)

include e he in
theorem exists_chief (hq : Function.Surjective q) [Representation.IsIrreducible ρ]
    (hρ : ∃ j v, ρ j v ≠ v) :
    ∃ s : ChiefSeries K, s.head = kernelNode q ∧ s.last = preimageNode q R ∧
      s.length = 1 ∧ s.noncentralTwoCount = 1 := by
  let := (Representation.irreducible_comp_surjective_iff q hq ρ).mpr inferInstance
  obtain ⟨s, hs0, hsl, hn, hc, _⟩ :=
    (coordinates q R ρ e he hq).exists_chief_refinement
      (kernel_le_preimage q R) (noncentral q ρ hq hρ)
  exact ⟨s, hs0, hsl, hn, hc⟩

end NoncentralChiefRefinement.ConjugationPullback

module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Contracts
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups.Sylow

/-!
# The two marked end-node parabolics in binary SL₅

The first and last standard flag stabilizers give actual subgroups of SL₅(2),
with the binary matrix-to-linear equivalence retaining their coordinate action.
Their two-cores are relative subgroups of the parabolics. The representations
below act on the literal normal fixed spaces through `quotientToInvariants`.

Sylow conjugacy places every elementary actor in both parabolics simultaneously.
The remaining source obligations are separate: excluding offenders in the radical,
and excluding quotient offenders when the restricted highest support is multiple.
The latter can use the existing SL₄ displacement producer; its required instance
is specified on the exact two fixed-space carriers. Neither obligation is proved
by its definition, nor is absolute irreducibility assumed.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Proposition 2.4, p.6, Theorem 3.1, p.13, and Proposition 4.7, pp.25–26;
Aschbacher–Smith K.3.2, printed pp.454–455.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation Representation.BinaryOffender
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry
open BinaryLinear.FiveFlagGeometry.SylowOvergroups

/-- The first and last simple roots, in the existing SL₅ numbering. -/
def node (e : Fin 2) : Fin 4 := if e = 0 then 0 else 3

/-- The literal three roots of the remaining SL₄ block. -/
def includedRoot (e : Fin 2) (i : Fin 3) : Fin 4 :=
  if e = 0 then i.succ else i.castSucc

/-- Restriction to the tail block at node 0, or the head block at node 3. -/
def restrictedSupport (e : Fin 2) (J : Finset (Fin 4)) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => includedRoot e i ∈ J)

/-- Root restriction agrees with deleting the selected end node. -/
theorem restrictedSupport_card (e : Fin 2) (J : Finset (Fin 4)) :
    (restrictedSupport e J).card = (J.erase (node e)).card := by
  revert e J
  decide +kernel

/-- The standard one-space or four-space stabilizer in the actual SL₅ group. -/
noncomputable def parabolic (e : Fin 2) : Subgroup SL5TenDimensional.Group :=
  (flagStabilizer standardBasis {node e}).comap (slEquivLinear 5).toMonoidHom

/-- The parabolic is exactly the corresponding block upper-triangular group. -/
theorem mem_parabolic_iff (e : Fin 2) (g : SL5TenDimensional.Group) :
    g ∈ parabolic e ↔ ∀ i j : Fin 5,
      (node e).val < i.val → j.val ≤ (node e).val → g.val i j = 0 := by
  change slEquivLinear 5 g ∈ flagStabilizer standardBasis {node e} ↔ _
  rw [mem_standard_flagStabilizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq, matrix, MulEquiv.symm_apply_apply]

/-- The two-core is taken inside the parabolic, never inside ambient SL₅. -/
noncomputable abbrev radical (e : Fin 2) : Subgroup (parabolic e) :=
  pCore 2 (parabolic e)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- The carrier of the actual radical fixed space. -/
noncomputable abbrev FixedSpace (e : Fin 2) :=
  Representation.invariants ((σ.comp (parabolic e).subtype).comp (radical e).subtype)

/-- The literal quotient action on the radical fixed vectors. -/
noncomputable abbrev quotientRepresentation (e : Fin 2) :=
  Representation.quotientToInvariants (σ.comp (parabolic e).subtype) (radical e)

/-- The still-unproved radical branch, required only when at least two roots
remain after deleting this end node. In particular this does not request the
separate endpoint-pair estimate. -/
def RadicalEstimate : Prop :=
  ∀ (e : Fin 2) (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    2 ≤ (J.erase (node e)).card →
    ∀ C : Subgroup (parabolic e), C ≤ radical e → IsElementaryTwo C →
    IsCubic (σ.comp (parabolic e).subtype) C →
    2 * rank C < fixedCodim (σ.comp (parabolic e).subtype) C

/-- The still-unproved Levi branch on the literal radical fixed space.
Its producer must establish the module and support comparisons. -/
def QuotientEstimate : Prop :=
  ∀ (e : Fin 2) (J : Finset (Fin 4)) (v : V), v ≠ 0 →
    SL5TenDimensional.Classification.LocalHighestVector σ J v →
    2 ≤ (restrictedSupport e J).card →
    ∀ A : Subgroup (parabolic e ⧸ radical e), IsElementaryTwo A →
    IsCubic (quotientRepresentation σ e) A →
    2 * rank A < fixedCodim (quotientRepresentation σ e) A

/-- The existing SL₄ producer, specialized to precisely the two fixed-space
carriers consumed by Levi induction. This is an explicit input until that
producer is complete and the assembly owner supplies it. -/
def FourDisplacementInput : Prop :=
  ∀ (e : Fin 2)
    (τ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
      (FixedSpace σ e)), Function.Injective τ → IsIrreducible τ →
      FourMultipleSupportDisplacement τ

/-- A single conjugate of an elementary actor lies in both standard end
parabolics: place it in the standard full-flag Sylow subgroup. -/
theorem exists_conjugate_le_parabolics
    (B : Subgroup SL5TenDimensional.Group) (hB : IsElementaryTwo B) :
    ∃ g : SL5TenDimensional.Group,
      ∀ e : Fin 2, B.map (MulAut.conj g).toMonoidHom ≤ parabolic e := by
  let : Finite (LinearGroup 5) :=
    Finite.of_injective (slEquivLinear 5).symm (slEquivLinear 5).symm.injective
  let E := slEquivLinear 5
  let : IsElementaryAbelian 2 B := hB.2
  have hp : IsPGroup 2 (B.map E.toMonoidHom) :=
    (IsElementaryAbelian.isPGroup 2 B).map E.toMonoidHom
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (LinearGroup 5) Q standardSylow
  have hconj : (B.map E.toMonoidHom).map (MulAut.conj a).toMonoidHom ≤
      standardBorel := by
    have hh := Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) hQ
    change (B.map E.toMonoidHom).map (MulAut.conj a).toMonoidHom ≤
      ((a • Q : Sylow 2 (LinearGroup 5)) : Subgroup (LinearGroup 5)) at hh
    simpa only [ha, standardSylow_coe] using hh
  refine ⟨E.symm a, ?_⟩
  intro e x hx
  obtain ⟨b, hb, rfl⟩ := hx
  have hb' := hconj (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom
    (Subgroup.mem_map_of_mem E.toMonoidHom hb))
  change a * E b * a⁻¹ ∈ standardBorel at hb'
  have hb'' : E ((MulAut.conj (E.symm a)) b) ∈ standardBorel := by
    simpa only [MulAut.conj_apply, map_mul, map_inv, E.apply_symm_apply] using hb'
  exact flagStabilizer_antitone standardBasis (Set.subset_univ _) hb''

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode

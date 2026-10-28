module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.Triality.ParabolicCover
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# The two residual local factors in the triality extension

The two subsystem Levis contain the two coordinates of the root torus.
Thus the two local factors themselves generate the triality carrier. Their
transported copies are characteristic residuals inside the transported
parabolics, so T normalizes them. Adjoining T gives another generating
family of proper T-overgroups, with two-group quotients over the factors.

The intrinsic two-core quotients of these actual factors are identified with
PSL₂ over GF(2^(3f)) and GF(2^f), respectively. The equivalences transport
the intrinsic cores, rather than imposing a quotient-family label.

Source: Aschbacher--Smith E.1.12, E.1.14(2), and F.1.12(I)(4),
printed pp.214,263--264 (`refs/quasithin.pdf`); GLS3 §2.6.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.Triality
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open ConcreteBruhat ConcreteBruhat.TorusCoordinates RadicalCoordinates
open scoped MatrixGroups

private theorem torus_le_localFactors (P : Parameters) (hp : P.prime = 2) :
    torus P ≤ localFactor P .arms ⊔ localFactor P .central := by
  intro x hx
  obtain ⟨⟨s, t⟩, he⟩ := (torusMulEquiv P hp).surjective ⟨x, hx⟩
  have hv := congrArg Subtype.val he
  rw [torusMulEquiv_val] at hv
  change toCarrier P (orbitElementary P hp (s, t)) = x at hv
  rw [← hv]
  change toCarrier P (foldedTorusElementary P hp .arms s *
    foldedTorusElementary P hp .central t) ∈ _
  rw [map_mul]
  exact mul_mem
    (mem_sup_left (levi_le_localFactor P hp .arms
      (LeviCommutators.torusActor_mem_levi P hp .arms s)))
    (mem_sup_right (levi_le_localFactor P hp .central
      (LeviCommutators.torusActor_mem_levi P hp .central t)))

/-- The literal residual factors already generate, including q = 2. -/
theorem localFactors_generate (P : Parameters) (hp : P.prime = 2) :
    localFactor P .arms ⊔ localFactor P .central = ⊤ := by
  apply top_unique
  rw [← parabolic_sup_binary P hp, parabolic_eq_localFactor_sup_torus P hp,
    parabolic_eq_localFactor_sup_torus P hp]
  exact sup_le (sup_le le_sup_left (torus_le_localFactors P hp))
    (sup_le le_sup_right (torus_le_localFactors P hp))

variable {G : Type*} [Group G] {f : ℕ} {hf : 0 < f}

def ambientLocalFactor (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) (a : Node) :
    Subgroup G := (localFactor (binaryParameters f hf) a).map (modelEmbedding L e)

def localOvergroup (L T : Subgroup G) (e : L ≃* BinaryCarrier f hf) (a : Node) :
    Subgroup G := ambientLocalFactor L e a ⊔ T

theorem ambientLocalFactor_le_parabolic (L : Subgroup G)
    (e : L ≃* BinaryCarrier f hf) (a : Node) :
    ambientLocalFactor L e a ≤ ambientParabolic L e a :=
  map_mono (localFactor_le_parabolic _ a)

theorem localOvergroup_le_parabolicOvergroup (L T : Subgroup G)
    (e : L ≃* BinaryCarrier f hf) (a : Node) :
    localOvergroup L T e a ≤ parabolicOvergroup L T e a :=
  sup_le_sup_right (ambientLocalFactor_le_parabolic L e a) T

theorem localOvergroups_generate (L T : Subgroup G) (e : L ≃* BinaryCarrier f hf)
    (hLT : L ⊔ T = ⊤) : localOvergroup L T e .arms ⊔ localOvergroup L T e .central = ⊤ := by
  have hlocal : ambientLocalFactor L e .arms ⊔ ambientLocalFactor L e .central = L := by
    rw [ambientLocalFactor, ambientLocalFactor, ← Subgroup.map_sup,
      localFactors_generate _ rfl, ← MonoidHom.range_eq_map, modelEmbedding_range]
  change (ambientLocalFactor L e .arms ⊔ T) ⊔ (ambientLocalFactor L e .central ⊔ T) = ⊤
  rw [sup_sup_sup_comm, sup_idem, hlocal, hLT]

def ambientLocalFactorEquiv (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) (a : Node) :
    ambientLocalFactor L e a ≃* localFactor (binaryParameters f hf) a :=
  ((localFactor (binaryParameters f hf) a).equivMapOfInjective
    (modelEmbedding L e) (modelEmbedding_injective L e)).symm

/-- The equivalence is between the intrinsic quotients of the embedded subgroups. -/
def ambientLocalFactorCoreQuotientEquiv (L : Subgroup G)
    (e : L ≃* BinaryCarrier f hf) (a : Node) :
    ambientLocalFactor L e a ⧸ pCore 2 (ambientLocalFactor L e a) ≃*
      localFactor (binaryParameters f hf) a ⧸ pCore 2 (localFactor (binaryParameters f hf) a) :=
  QuotientGroup.congr _ _ (ambientLocalFactorEquiv L e a)
    (pCore_map_iso 2 (ambientLocalFactorEquiv L e a))

def armsCoreQuotientEquiv (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    ambientLocalFactor L e .arms ⧸ pCore 2 (ambientLocalFactor L e .arms) ≃*
      PSL(2, GaloisField 2 (3 * f)) :=
  (ambientLocalFactorCoreQuotientEquiv L e .arms).trans
    (localFactorArmsQuotientEquivPSL2 (binaryParameters f hf) rfl)

def centralCoreQuotientEquiv (L : Subgroup G) (e : L ≃* BinaryCarrier f hf) :
    ambientLocalFactor L e .central ⧸ pCore 2 (ambientLocalFactor L e .central) ≃*
      PSL(2, GaloisField 2 f) :=
  (ambientLocalFactorCoreQuotientEquiv L e .central).trans
    (localFactorCentralQuotientEquivPSL2 (binaryParameters f hf) rfl)

theorem ambientLocalFactor_eq_residual (L : Subgroup G)
    (e : L ≃* BinaryCarrier f hf) (a : Node) :
    ambientLocalFactor L e a =
      (primeToResidual 2 (ambientParabolic L e a)).map (ambientParabolic L e a).subtype :=
  map_embedded_primeToResidual_of_hom 2 _ _

variable [Finite G]

theorem sylow_normalizes_ambientLocalFactor (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    (T : Subgroup G) ≤ normalizer (ambientLocalFactor L e a : Set G) := by
  rw [ambientLocalFactor_eq_residual]
  exact (sylow_normalizes_ambientParabolic L T e he a).trans
    (normalizer_le_normalizer_characteristic_image _ _)

theorem ambientLocalFactor_normal_in_overgroup (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    ((ambientLocalFactor L e a).subgroupOf (localOvergroup L T e a)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (sup_le (ambientLocalFactor L e a).le_normalizer
      (sylow_normalizes_ambientLocalFactor L T e he a))

theorem localOvergroup_quotient_isTwoGroup (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) :
    let _ := ambientLocalFactor_normal_in_overgroup L T e he a
    IsPGroup 2 ((localOvergroup L T e a) ⧸
      (ambientLocalFactor L e a).subgroupOf (localOvergroup L T e a)) := by
  let _ := ambientLocalFactor_normal_in_overgroup L T e he a
  apply isPGroup_quotient_of_sup_eq_top _
    ((T : Subgroup G).subgroupOf (localOvergroup L T e a)) T.isPGroup'.comap_subtype
  rw [← subgroupOf_sup (show ambientLocalFactor L e a ≤ localOvergroup L T e a
    from le_sup_left) (show (T : Subgroup G) ≤ localOvergroup L T e a from le_sup_right)]
  exact subgroupOf_self _

theorem localOvergroup_ne_top (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* BinaryCarrier f hf)
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent (binaryParameters f hf)) (a : Node) : localOvergroup L T e a ≠ ⊤ := by
  intro h
  apply parabolicOvergroup_ne_top L T e he a
  exact top_unique (h ▸ localOvergroup_le_parabolicOvergroup L T e a)

end CFSG.Quasithin.ChapterE.ExceptionalValues.Triality

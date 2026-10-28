module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.Definitions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.BlockNormalizer.Concrete.Structure
public import Theory.Frattini.PGroup
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PCoreSurjective

/-!
# The literal HS normalizer preimage and its Frattini section

For an actual central-quotient equivalence with HS, `M` is the inverse image
of the normalizer of the concrete elementary eight. Its intrinsic two-core
is `Q`; `E` is the image of Φ(Q) inside M. The group `Qbar` is the actual
image of Q in M/E, with an explicit equivalence Q/Φ(Q) ≃ Qbar. In particular
Qbar is elementary abelian, without any model-dimension assumption.

These definitions fix the maps used in the last HS paragraph of
Aschbacher–Smith I.2.2(5), printed p.412 / PDF p.423. Identifying the model
two-core with 4³, proving that Q is abelian, and identifying its module of
dimension four remain separate mathematical obligations.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS.BlockNormalizer
variable {K : Type*} [Group K]

/-- The given central quotient map, followed by the actual HS equivalence. -/
def modelMap (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    K →* Sporadic.LeechRelated.HS.Carrier :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center K))

/-- The inverse image of the concrete elementary-eight normalizer. -/
def M (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) : Subgroup K :=
  baseNormalizer.comap (modelMap e)

/-- The intrinsic two-core of the actual preimage. -/
def Q (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) : Subgroup (M e) :=
  pCore 2 (M e)

/-- Its Frattini subgroup, embedded into the preimage M. -/
def E (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) : Subgroup (M e) :=
  (frattini (Q e)).map (Q e).subtype

instance Q_characteristic (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (Q e).Characteristic := by unfold Q; infer_instance

instance E_characteristic (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (E e).Characteristic := by unfold E; infer_instance

/-- Q as a normal subgroup of the literal quotient M/E. -/
def Qbar (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Subgroup ((M e) ⧸ E e) := (Q e).map (QuotientGroup.mk' (E e))

instance Qbar_normal (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (Qbar e).Normal :=
  Normal.map inferInstance _ (QuotientGroup.mk'_surjective (E e))

/-- The canonical map from Q to its image in M/E. -/
def coreMap (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Q e →* Qbar e :=
  ((QuotientGroup.mk' (E e)).comp (Q e).subtype).codRestrict (Qbar e)
    (fun q => mem_map_of_mem _ q.property)

theorem coreMap_surjective (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Function.Surjective (coreMap e) := by
  rintro ⟨x, q, hq, rfl⟩
  exact ⟨⟨q, hq⟩, rfl⟩

theorem coreMap_ker (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (coreMap e).ker = frattini (Q e) := by
  ext q
  change (coreMap e q = 1) ↔ _
  rw [← Subtype.val_inj]
  change QuotientGroup.mk' (E e) (q : M e) = 1 ↔ _
  constructor
  · intro hq
    obtain ⟨a, ha, he⟩ := (QuotientGroup.eq_one_iff (q : M e)).mp hq
    have h : a = q := Subtype.ext he
    exact h ▸ ha
  · intro hq
    exact (QuotientGroup.eq_one_iff (q : M e)).mpr ⟨q, hq, rfl⟩

/-- The actual Frattini quotient is identified with its embedded image. -/
noncomputable def frattiniEquiv
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    (Q e ⧸ frattini (Q e)) ≃* Qbar e :=
  (QuotientGroup.quotientMulEquivOfEq (coreMap_ker e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (coreMap e) (coreMap_surjective e))

theorem frattiniEquiv_mk
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) (q : Q e) :
    frattiniEquiv e (QuotientGroup.mk' (frattini (Q e)) q) = coreMap e q := rfl

instance Qbar_elementary [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    IsElementaryAbelian 2 (Qbar e) := by
  let : Fact (IsPGroup 2 (Q e)) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 (Q e ⧸ frattini (Q e)) :=
    isElementaryAbelian_quotient_frattini
  exact IsElementaryAbelian.of_surjective (frattiniEquiv e).toMonoidHom
    (frattiniEquiv e).surjective

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal

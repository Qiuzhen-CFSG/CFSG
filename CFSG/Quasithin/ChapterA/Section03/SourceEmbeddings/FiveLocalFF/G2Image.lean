module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# The literal G₂ image of a local alternating-five section

The solvable global kernel preserves the local C-component condition at
the image of the original full Sylow. A two-group restricted kernel
transports the given alternating-five marking elementwise. The G₂ sieve
then supplies field order four and the actual short or long parabolic
residual. The binary derived row is excluded by its order.

Source: Aschbacher–Smith 10.2.9, printed pp.751–752.
-/

public section
noncomputable section
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- The original marking transported through the restricted two-kernel. -/
def image_five_equiv (f : G →* Model F) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    ((L.map f) ⧸ pCore 2 (L.map f)) ≃* alternatingGroup (Fin 5) :=
  ((f.subgroupMap L).quotientPCoreEquivOfSurjective
    (f.subgroupMap_surjective L) hk).symm.trans e

omit [CharP F 2] in
/-- The transported marking agrees on every original element. -/
theorem image_five_equiv_apply (f : G →* Model F) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (l : L) :
    image_five_equiv f L hk e
      (QuotientGroup.mk' (pCore 2 (L.map f)) (f.subgroupMap L l)) =
        e (QuotientGroup.mk' (pCore 2 L) l) := by
  change e (((f.subgroupMap L).quotientPCoreEquivOfSurjective
    (f.subgroupMap_surjective L) hk).symm
    (QuotientGroup.mk' (pCore 2 (L.map f)) (f.subgroupMap L l))) = _
  rw [← MonoidHom.quotientPCoreEquivOfSurjective_mk
    (f.subgroupMap L) (f.subgroupMap_surjective L) hk l, MulEquiv.symm_apply_apply]

/-- The literal reduced-action image lies in a field-four G₂ parabolic residual. -/
theorem five_section_image (hq : 2 < Nat.card F)
    (f : G →* Model F) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (hproper : L.map f ≠ ⊤)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : Model F,
      (L.map f).map (MulAut.conj g).toMonoidHom = local₁ ∨
      (L.map f).map (MulAut.conj g).toMonoidHom = local₂ := by
  let := hks
  exact five_section_placement hq (S.mapSurjective hf) (L.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hL f)
    hproper (image_five_equiv f L hk e)

omit [CharP F 2] in
/-- A map with two-group restricted kernel cannot send the marked subgroup
into the binary derived carrier. -/
theorem binary_derived_image_excluded (hF : Nat.card F = 2)
    (f : G →* commutator (Model F)) (L : Subgroup G)
    (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) : False :=
  binary_derived_excluded hF (L.map f)
    (((f.subgroupMap L).quotientPCoreEquivOfSurjective
      (f.subgroupMap_surjective L) hk).symm.trans e)

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2

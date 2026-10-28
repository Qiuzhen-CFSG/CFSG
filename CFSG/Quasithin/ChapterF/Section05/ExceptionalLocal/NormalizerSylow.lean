module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionRoots
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Sylow transport for the exceptional F.5 normalizer calculation

Fusion of the marked graph involution f with t identifies their actual
centralizers. Sylow conjugacy transports the literal T-centralizer model
D8 × D8 to any Sylow R of C_G(f). The common Tf has index two in R;
its actual ambient image is consequently normalized by R. The endpoint
cores lie in this same Tf, by normal p-subgroup containment in a Sylow.

Source: Aschbacher--Smith F.5.4(2--3), printed p.301. The earlier FusionFacts
producer remains explicit; no normalizer structure or recognition is assumed.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G)
  (hf : FusionFacts c i z t)
include hf

theorem normalizer_R_iso (R : Sylow 2 (C c i)) :
    Nonempty (Rimage c i R ≃* DihedralGroup 4 × DihedralGroup 4) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hf.graph_fuses_t
  let e : C c i ≃* centralizer ({t} : Set G) :=
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g)
      (Source.graphElement c i)).trans
        (MulEquiv.subgroupCongr (congrArg (fun x : G => centralizer ({x} : Set G)) hg))
  let R' : Sylow 2 (centralizer ({t} : Set G)) := R.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨S,hS⟩ := hf.t_sylow
  have hmap : (S : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype = Tcentralizer c i t := by
    rw [hS,subgroupOf_map_subtype]
    rfl
  obtain ⟨eT⟩ := hf.t_centralizer_iso
  exact ⟨((R : Subgroup (C c i)).equivMapOfInjective _ (C c i).subtype_injective).symm.trans
    (((R : Subgroup (C c i)).equivMapOfInjective e.toMonoidHom e.injective).trans
      ((R'.equiv S).trans (((S : Subgroup (centralizer ({t} : Set G))).equivMapOfInjective _
        (centralizer ({t} : Set G)).subtype_injective).trans
          ((MulEquiv.subgroupCongr hmap).trans eT))))⟩

theorem normalizer_R_card (R : Sylow 2 (C c i)) : Nat.card (Rimage c i R) = 64 := by
  obtain ⟨e⟩ := normalizer_R_iso c i z t hf R
  rw [Nat.card_congr e.toEquiv,Nat.card_prod,DihedralGroup.nat_card]

omit [Finite G] in
theorem normalizer_TfImage_card : Nat.card (TfImage c i) = 32 := by
  rw [TfImage,card_map_of_injective (C c i).subtype_injective,hf.tf_card]

omit [Finite G] in
theorem normalizer_A_le_TfImage (b : Bool) : A c i b ≤ TfImage c i := by
  obtain ⟨S,hS⟩ := hf.tf_sylow b
  rw [←hS]
  exact pCoreIn_le_sylow _ S

omit hf [Finite G] in
theorem normalizer_TfImage_le_Rimage (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) : TfImage c i ≤ Rimage c i R :=
  map_mono hR

theorem normalizer_Tf_relIndex (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) :
    (TfImage c i).relIndex (Rimage c i R) = 2 := by
  have he := ((TfImage c i).subgroupOf (Rimage c i R)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (normalizer_TfImage_le_Rimage c i R hR)).toEquiv] at he
  change Nat.card (TfImage c i) * (TfImage c i).relIndex (Rimage c i R) =
    Nat.card (Rimage c i R) at he
  rw [normalizer_TfImage_card c i z t hf,normalizer_R_card c i z t hf] at he
  omega

theorem normalizer_R_normalizes_Tf (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) :
    Rimage c i R ≤ normalizer (TfImage c i : Set G) := by
  apply (normal_subgroupOf_iff_le_normalizer
    (normalizer_TfImage_le_Rimage c i R hR)).mp
  exact normal_of_index_eq_two (normalizer_Tf_relIndex c i z t hf R hR)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal

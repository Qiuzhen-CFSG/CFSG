module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionSymplectic
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.SourceAlternatives
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.NormalSource
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceSolvableSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Constructing original Hermitian source witnesses

The original component catalogue supplies a marked dihedral, linear or Suzuki
pair outside its two normal symplectic rows. Normalization by the distinguished
maximal subgroup makes the nonbinary symplectic image its full central root
plane. Its opposite pair lifts through the full maximal core. The binary row
supplies either a dihedral pair or a marked Sp4(2) pair. Returning-conjugate
centralization excludes both symplectic pairs on the original action.

The center marking is transported from any Sylow to the actual image Sylow
using conjugacy inside the normalizer of the marked subgroup. All quotient
maps, internal conjugators and Sylow intersections are preserved. Positive
weak closure supplies the returning-conjugate condition in the ambient H.
A degree-one witness then supplies the existing selected dihedral pair.

This constructs the geometric witness, including its literal quotient model.
It does not assert divisibility of its degree by generationParameter H. That
additional field of the existing Family interface and the field-four endgame
remain obligations of the Hermitian source assembly. No numerical equality is
inferred from a quotient model.

Source: Aschbacher--Smith E.2.7--9, E.2.13(6) and 8.2.2,
printed pp.218--225,714--715, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open Witnesses Witnesses.BenderPlacement
variable {X : Type*} [Group X] [Finite X]

private theorem sylow_centralizes_of_normalizes (E : Subgroup X) (R S : Sylow 2 X)
    (hR : (R : Subgroup X) ≤ normalizer (E : Set X))
    (hS : (S : Subgroup X) ≤ centralizer (E : Set X)) :
    (R : Subgroup X) ≤ centralizer (E : Set X) := by
  let N := normalizer (E : Set X)
  have hSN : (S : Subgroup X) ≤ N := hS.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨x,hx⟩ := MulAction.exists_smul_eq N (S.subtype hSN) (R.subtype hR)
  rw [Sylow.smul_subtype] at hx
  have he : (S : Subgroup X).map (MulAut.conj x.val).toMonoidHom = R :=
    congrArg Sylow.toSubgroup (Sylow.subtype_injective hx)
  have hc := (map_mono (f := (MulAut.conj x.val).toMonoidHom) hS).trans
    (map_centralizer_le_centralizer_image (E : Set X) (MulAut.conj x.val).toMonoidHom)
  change (S : Subgroup X).map (MulAut.conj x.val).toMonoidHom ≤
    centralizer (E.map (MulAut.conj x.val).toMonoidHom : Set X) at hc
  have hE : E.map (MulAut.conj x.val).toMonoidHom = E :=
    mem_normalizer_iff_map_conj_eq.mp x.property
  rwa [he,hE] at hc

/-- A marked symplectic pair is impossible under the original returning-conjugate
condition. Its center marking may use any Sylow; normality recovers the original one. -/
theorem original_pair_symplectic_excluded
    {R : Sylow 2 X} {M V : Subgroup X} [IsElementaryAbelian 2 V]
    (w : QuotientLift.Pair R M V) (hVR : V ≤ R)
    (hRV : (R : Subgroup X) ≤ normalizer (V : Set X))
    (hcore : V ≤ M.pCoreIn 2) (hNV : normalizer (V : Set X) ≤ M)
    (hMV : M ≤ normalizer (V : Set X))
    (hfit : generalizedFitting X = pCore 2 X)
    (hret : ∀ x : X, V.map (MulAut.conj x).toMonoidHom ≤ R →
      V.map (MulAut.conj x).toMonoidHom ≤ centralizer (V : Set X))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (m : ℕ) (hm : 0 < m) (hF : Nat.card F = 2^m)
    (ξ : (w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore) ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hVS : (V.subgroupOf w.subgroup).map (ξ.toMonoidHom.comp
      (QuotientGroup.mk' (M.subgroupOf w.subgroup).normalCore)) ≤
      (center S).map (S : Subgroup _).subtype) : False := by
  let hp := w.hypotheses hVR hRV hcore hNV
  have hproper := w.proper_of_quotient_card_ne_one hNV (by
    rw [Nat.card_congr ξ.toEquiv]
    have hd : 2 ∣ Nat.card (Theory.SpecificGroups.SymplecticFour.Sp F) := by
      rw [Theory.SpecificGroups.SymplecticFour.card_sp,hF]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        ((dvd_pow_self 2 (by omega : m ≠ 0)).trans (dvd_pow_self _ (by decide : 4 ≠ 0))) _) _
    intro he
    rw [he] at hd
    norm_num at hd)
  let q := QuotientGroup.mk' (M.subgroupOf w.subgroup).normalCore
  let f := ξ.toMonoidHom.comp q
  let Q := w.sylow.mapSurjective (f := f) (ξ.surjective.comp (QuotientGroup.mk'_surjective _))
  let E := (V.subgroupOf w.subgroup).map f
  have hEQ : E ≤ Q := map_mono hp.le_sylow
  have hQN : (Q : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) ≤
      normalizer (E : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) :=
    (map_mono (f := f) hp.sylow_le_normalizer).trans (le_normalizer_map f)
  have hSC : (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) ≤
      centralizer (E : Set (Theory.SpecificGroups.SymplecticFour.Sp F)) := by
    apply le_centralizer_iff.mpr
    intro v hv s hs
    obtain ⟨z,hz,rfl⟩ := hVS hv
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨s,hs⟩)
  have hQC := sylow_centralizes_of_normalizes E Q S hQN hSC
  have hEcenter : E ≤ (center Q).map (Q : Subgroup _).subtype := by
    intro v hv
    refine ⟨⟨v,hEQ hv⟩,?_,rfl⟩
    exact mem_center_iff.mpr (fun s => Subtype.ext ((hQC s.property) v hv).symm)
  have hcenter : (V.subgroupOf w.subgroup).map q ≤
      (center ((w.sylow : Subgroup w.subgroup).map q)).map
        ((w.sylow : Subgroup w.subgroup).map q).subtype := by
    apply (map_le_map_iff_of_injective (f := ξ.toMonoidHom) ξ.injective).mp
    rw [map_embeddedCenter _ _ ξ.injective,map_map,map_map]
    exact hEcenter
  have hMN : M.subgroupOf w.subgroup ≤ normalizer (V.subgroupOf w.subgroup : Set w.subgroup) := by
    rw [←subgroupOf_normalizer_eq w.le]
    exact comap_mono hMV
  have hret' : ∀ x : w.subgroup,
      (V.subgroupOf w.subgroup).map (MulAut.conj x).toMonoidHom ≤ w.sylow →
      (V.subgroupOf w.subgroup).map (MulAut.conj x).toMonoidHom ≤
        centralizer (V.subgroupOf w.subgroup : Set w.subgroup) := by
    intro x hx
    have he : ((V.subgroupOf w.subgroup).map (MulAut.conj x).toMonoidHom).map w.subgroup.subtype =
        V.map (MulAut.conj x.val).toMonoidHom := by
      rw [map_map]
      have hh : w.subgroup.subtype.comp (MulAut.conj x).toMonoidHom =
          (MulAut.conj x.val).toMonoidHom.comp w.subgroup.subtype := by ext y; rfl
      rw [hh,←map_map,map_subgroupOf_eq_of_le w.le]
    have ht : V.map (MulAut.conj x.val).toMonoidHom ≤ R := by
      rw [←he]
      exact (map_mono hx).trans (w.sylow_eq.le.trans inf_le_left)
    intro a ha b hb
    exact Subtype.ext (hret x.val ht (he ▸ mem_map_of_mem w.subgroup.subtype ha) b.val hb)
  exact pair_symplectic_excluded hp hproper (w.fitting hRV hfit) hMN hret' m hm hF ξ hcenter

/-- Lift the marked quotient pair through the entire minimal-parabolic core
before applying the returning-conjugate contradiction. -/
theorem original_quotient_pair_symplectic_excluded
    (R : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver R ⊤)
    (V : Subgroup X) [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (hcore : V ≤ (ChapterB.minimalParabolicMax R hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore R hP)
    (hMV : ChapterB.minimalParabolicMax R hP ≤ normalizer (V : Set X))
    (hfit : generalizedFitting X = pCore 2 X)
    (hret : ∀ x : X, V.map (MulAut.conj x).toMonoidHom ≤ R →
      V.map (MulAut.conj x).toMonoidHom ≤ centralizer (V : Set X))
    (w : QuotientLift.Pair
      (R.mapSurjective (QuotientGroup.mk'_surjective (ChapterB.minimalParabolicCore R hP)))
      ((ChapterB.minimalParabolicMax R hP).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP)))
      (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (m : ℕ) (hm : 0 < m) (hF : Nat.card F = 2^m)
    (ξ : (w.subgroup ⧸ (((ChapterB.minimalParabolicMax R hP).map
      (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))).subgroupOf w.subgroup).normalCore) ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hVS : ((V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore R hP))).subgroupOf w.subgroup).map
      (ξ.toMonoidHom.comp (QuotientGroup.mk' _)) ≤ (center S).map (S : Subgroup _).subtype) : False := by
  let M := ChapterB.minimalParabolicMax R hP
  let J := ChapterB.minimalParabolicCore R hP
  let q := QuotientGroup.mk' J
  have hRV := (ChapterB.minimalParabolicMax_spec R hP).2.trans hMV
  have hvn := (normal_subgroupOf_iff_le_normalizer hVR).mpr hRV
  have hNV := minimalParabolic_normalizer_le R hP V (IsElementaryAbelian.isPGroup 2 V) hRV hout
  obtain ⟨w',r,_,hr,e,he⟩ := QuotientLift.lift_pair R hP V hVR hvn hcore w
  have hrV : (V.subgroupOf w'.subgroup).map r = (V.map q).subgroupOf w.subgroup := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      change (r x : X ⧸ J) ∈ V.map q
      rw [hr]
      exact mem_map_of_mem q hx
    · intro hy
      obtain ⟨x,hx,hxy⟩ := hy
      exact ⟨⟨x,w'.le hx⟩,hx,Subtype.ext (by rw [hr]; exact hxy)⟩
  have hemap : (e.trans ξ).toMonoidHom.comp (QuotientGroup.mk' _) =
      (ξ.toMonoidHom.comp (QuotientGroup.mk' _)).comp r := by
    apply MonoidHom.ext
    intro x
    change ξ (e (QuotientGroup.mk' _ x)) = ξ (QuotientGroup.mk' _ (r x))
    rw [he]
  apply original_pair_symplectic_excluded w' hVR hRV hcore hNV hMV hfit hret m hm hF (e.trans ξ) S
  rw [hemap,←map_map,hrV]
  exact hVS

/-- The entire original source catalogue constructs a nonsymplectic witness
when the maximal subgroup normalizes V and returning conjugates centralize it.
The binary and nonbinary symplectic source rows are both discharged. -/
theorem exists_original_witness_of_normalized_returns
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (R : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver R ⊤)
    (V : Subgroup X) [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (hcore : V ≤ (ChapterB.minimalParabolicMax R hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore R hP)
    (hMV : ChapterB.minimalParabolicMax R hP ≤ normalizer (V : Set X))
    (hfit : generalizedFitting X = pCore 2 X)
    (hret : ∀ x : X, V.map (MulAut.conj x).toMonoidHom ≤ R →
      V.map (MulAut.conj x).toMonoidHom ≤ centralizer (V : Set X)) :
    ∃ n : ℕ, Nonempty (OriginalWitness R (ChapterB.minimalParabolicMax R hP) V n) := by
  have hRV := (ChapterB.minimalParabolicMax_spec R hP).2.trans hMV
  have hvn := (normal_subgroupOf_iff_le_normalizer hVR).mpr hRV
  have hNV := minimalParabolic_normalizer_le R hP V (IsElementaryAbelian.isPGroup 2 V) hRV hout
  have hTI : ∀ x ∈ ChapterB.minimalParabolicMax R hP,
      V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨ V.map (MulAut.conj x).toMonoidHom = V := by
    intro x hx
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hMV hx))
  rcases source_original_witness_or_symplectic hX R hP V hVR hvn hcore hout hTI with hw | ⟨K,hK,hN,hgen,hm⟩
  · exact hw
  let := hN
  have hs : ¬ Group.IsSolvable X := by
    intro hsol
    let := hsol
    exact hK.not_isSolvable (Group.isSolvable_of_isSolvable_injective K.subtype_injective)
  rcases hm with hmodel | hmodel
  · obtain ⟨m,hm,F,hF,hfin,hcard,⟨e⟩⟩ := hmodel
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
    obtain ⟨w⟩ := Witnesses.SymplecticFour.source_normal_full_quotient R hP hs K hK hgen
      (by omega) hcard e V hVR hcore hout hMV
    exact (original_quotient_pair_symplectic_excluded R hP V hVR hcore hout hMV hfit hret w.pair
      m (by omega) hcard w.quotientModel
      (Theory.SpecificGroups.SymplecticFour.unipotentSylow hcard (by omega))
      (w.quotient_center hcard (by omega))).elim
  · obtain ⟨eK⟩ := hmodel
    rcases Witnesses.SymplecticFour.Binary.source_original R hP hs K hK hgen eK V hVR hvn hcore hout
      with hw | ⟨w,ξ,S,hVS⟩
    · exact ⟨1,hw⟩
    · exact (original_pair_symplectic_excluded w hVR hRV hcore hNV hMV hfit hret
        1 (by decide) (by simp) ξ S hVS).elim

variable {G : Type*} [Group G] [Finite G]
/-- Actual witness construction in the original H, preserving the original
Sylow intersection, subgroup V and full maximal-core quotient. -/
theorem exists_original_witness_of_positive_weak_closure
    {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hfit : generalizedFitting H = pCore 2 H)
    (hMV : H ⊓ M ≤ normalizer (V : Set G)) (hw : 0 < globalW V T) :
    ∃ R : Sylow 2 H, (R : Subgroup H) = T.subgroupOf H ∧
      ∃ n : ℕ, Nonempty (OriginalWitness R (M.subgroupOf H) (V.subgroupOf H) n) := by
  have hVH := h.le_sylow.trans h.le_ambient
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h.minimal
  obtain ⟨hVR,_,hcore,hout⟩ := intrinsic_source_data h R hR hP hM
  have hMV' : ChapterB.minimalParabolicMax R hP ≤ normalizer (V.subgroupOf H : Set H) := by
    rw [←hM,←subgroupOf_normalizer_eq hVH]
    exact fun x hx => hMV ⟨x.property,hx⟩
  have hret : ∀ x : H, (V.subgroupOf H).map (MulAut.conj x).toMonoidHom ≤ R →
      (V.subgroupOf H).map (MulAut.conj x).toMonoidHom ≤ centralizer (V.subgroupOf H : Set H) := by
    intro x hx
    have hh := local_conjugates_centralize H T V hVH hw x⁻¹
    simp only [inv_inv] at hh
    exact hh (hR ▸ hx)
  obtain ⟨n,hw⟩ := exists_original_witness_of_normalized_returns h.sqtk R hP
    (V.subgroupOf H) hVR hcore hout hMV' hfit hret
  rw [←hM] at hw
  exact ⟨R,hR,n,hw⟩

/-- A degree-one original witness supplies the actual selected dihedral pair.
The divisibility clause follows from degree one, without a quotient-parameter rule. -/
theorem selected_one_of_original_witness
    {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 KnownSimple.IsKnownSimple H T M V)
    (hfit : generalizedFitting H = pCore 2 H)
    (R : Sylow 2 H) (hR : (R : Subgroup H) = T.subgroupOf H)
    {n : ℕ} (w : OriginalWitness R (M.subgroupOf H) (V.subgroupOf H) n)
    (hd : w.degree = 1)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I), Selected H T M V I 1 i S := by
  have hw : Nonempty (Witnesses.Solvable.Witness R (M.subgroupOf H) (V.subgroupOf H)) := by
    cases w.model with
    | dihedral he p a hp hp2 ha e =>
      exact ⟨⟨w.pair.subgroup,w.pair.le,w.pair.conjugator,w.pair.generate,
        w.pair.sylow,w.pair.sylow_eq,w.pair.core_two_closed,p,a,hp,hp2,ha,⟨e⟩⟩⟩
    | linear hk e hb => omega
    | suzuki m hm he e hb => omega
  obtain ⟨w'⟩ := hw
  have hVH := h.le_sylow.trans h.le_ambient
  have hne : V ≠ ⊥ := by intro he; exact h.outside_core (he ▸ bot_le)
  obtain ⟨I,f,hr⟩ := family_of_dihedral_witness hVH h.elementary hne h.le_sylow R hR w'
  obtain ⟨i,S,s⟩ := exists_selected_of_rank_one_family h hfit f hr hq hTI hNV
  exact ⟨I,i,S,s⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

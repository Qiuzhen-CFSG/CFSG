module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Four
public import Theory.AtlasPort.LinearGroups.G2.ShortLocalElementary
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction

/-!
# Core normality for every prepared G₂ maximal overcomponent

Let K = O²(H), Q = O₂(K) and R = O₂(J), where J is a maximal local
overcomponent of K. The original common-Sylow geometry gives R ≤ Q.
The existing short-root calculation puts every K-normal elementary
subgroup in C_G(K), so Ω₁(Z(R)) ≤ Ω₁(Z(Q)). Characteristic two in J
supplies the reverse containment. Thus J normalizes the nontrivial
characteristic subgroup Ω₁(Z(Q)).

Source 1.2.7 makes J a C-component of its normalizer. Uniqueness of a
C-component containing the nonsolvable K then makes the whole N_G(K)
normalize J. In particular the original right parabolic normalizes R.
Its full-torus core dichotomy forces R = Q, including at field four.
This removes the nonnormal-core branch of the earlier G₂ alternative,
retaining the actual cubic and quotient shortlist in the remaining case.

The field-four representation exclusions, other outstanding maximality
rows, exhaustive F.1.12 comparison and ambient recognition remain open.
The companion applies both results to the literal Chapter12 pair, with
original S, whole overlap, and the uniqueness premise unchanged.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653, and 1.2.7, p.506
(`refs/quasithin.pdf`). The imported root calculation retains the ATLAS
attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Atlas.G2 Atlas.G2.LieParabolicSetup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] in
private theorem normal_elementary_central {K E : Subgroup G}
    (a : K ≃* local₁ (F := F)) [IsElementaryAbelian 2 E]
    (hEK : E ≤ K) (hn : K ≤ normalizer (E : Set G)) :
    E ≤ centralizer (K : Set G) := by
  let f : K →* Model F := (local₁ (F := F)).subtype.comp a.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp a.injective
  have hfr : f.range = local₁ (F := F) := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr a.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  let D := (E.subgroupOf K).map f
  let : IsElementaryAbelian 2 (E.subgroupOf K) := IsElementaryAbelian.subgroupOf hEK
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map f
  let : (E.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hn
  have hD : D ≤ local₁ (F := F) := hfr ▸ map_le_range f _
  have hND : local₁ ≤ normalizer (D : Set (Model F)) := by
    have hh := (E.subgroupOf K).le_normalizer_map f
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,hfr] using hh
  have hz := elementary_normal_short_local_le_highestRoot D hD hND
  intro x hx
  rw [mem_centralizer_iff]
  intro k hk
  have hh := hz (mem_map_of_mem f (show (⟨x,hEK hx⟩ : K) ∈ E.subgroupOf K from hx))
  obtain ⟨b,hb⟩ := hh
  have hc : f ⟨k,hk⟩ * f ⟨x,hEK hx⟩ = f ⟨x,hEK hx⟩ * f ⟨k,hk⟩ := by
    rw [←hb]
    exact mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA b.toAdd
      (hfr ▸ (show f ⟨k,hk⟩ ∈ f.range from ⟨⟨k,hk⟩,rfl⟩)))
  have he : (⟨k,hk⟩ : K) * ⟨x,hEK hx⟩ = ⟨x,hEK hx⟩ * ⟨k,hk⟩ := by
    apply hf
    simpa only [map_mul] using hc
  exact congrArg Subtype.val he


omit [Finite G] in
private theorem overcomponent_omega_center {K J : Subgroup G}
    (a : K ≃* local₁ (F := F)) (hKJ : K ≤ J)
    (hchar : J ⊓ centralizer (J.pCoreIn 2 : Set G) ≤ J.pCoreIn 2)
    (hRQ : J.pCoreIn 2 ≤ K.pCoreIn 2) :
    omegaCenterIn (J.pCoreIn 2) = omegaCenterIn (K.pCoreIn 2) := by
  let R := J.pCoreIn 2
  let Q := K.pCoreIn 2
  let E := omegaCenterIn R
  have hEK : E ≤ K := (map_subtype_le _).trans (hRQ.trans (map_subtype_le _))
  have hKE : K ≤ normalizer (E : Set G) := hKJ.trans (J.le_normalizer.trans
    ((normalizer_le_normalizer_characteristic_image J (pCore 2 J)).trans
      (normalizer_le_normalizer_omegaCenterIn R)))
  have hcent : E ≤ centralizer (K : Set G) := normal_elementary_central a hEK hKE
  apply le_antisymm
  · intro x hx
    obtain ⟨hxR,_,hs⟩ := (mem_omegaCenterIn_iff R x).mp hx
    exact (mem_omegaCenterIn_iff Q x).mpr
      ⟨hRQ hxR,centralizer_le (map_subtype_le _) (hcent hx),hs⟩
  · intro x hx
    obtain ⟨hxQ,hxc,hs⟩ := (mem_omegaCenterIn_iff Q x).mp hx
    have hcR : x ∈ centralizer (R : Set G) := centralizer_le hRQ hxc
    exact (mem_omegaCenterIn_iff R x).mpr
      ⟨hchar ⟨hKJ (map_subtype_le _ hxQ),hcR⟩,hcR,hs⟩

private theorem maximal_normalizes_of_omega_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J : Subgroup G}
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : K ≤ J)
    (hR : J.pCoreIn 2 ≠ ⊥)
    (he : omegaCenterIn (J.pCoreIn 2) = omegaCenterIn (K.pCoreIn 2)) :
    normalizer (K : Set G) ≤ normalizer (J : Set G) := by
  let R := J.pCoreIn 2
  let Z := omegaCenterIn R
  let N := normalizer (Z : Set G)
  have hZN : Z ≠ ⊥ := by
    let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hR
    exact fun hz => omega_center_ne_bot (G := R) (isPGroup_pCoreIn 2 J)
      ((Subgroup.map_eq_bot_iff_of_injective _ R.subtype_injective).mp hz)
  have hNN : normalizer (K : Set G) ≤ N := by
    change normalizer (K : Set G) ≤ normalizer (omegaCenterIn R : Set G)
    rw [he]
    exact (normalizer_le_normalizer_characteristic_image K (pCore 2 K)).trans
      (normalizer_le_normalizer_omegaCenterIn (K.pCoreIn 2))
  have hJN : J ≤ N := J.le_normalizer.trans
    ((normalizer_le_normalizer_characteristic_image J (pCore 2 J)).trans
      (normalizer_le_normalizer_omegaCenterIn R))
  have hKN : K ≤ N := hKJ.trans hJN
  have hTN : (T : Subgroup G) ≤ N := hTK.trans hNN
  have hN : N ∈ Chapter1.H G :=
    Chapter1.mem_H_of_isTwoLocal ⟨Z,hZN,IsElementaryAbelian.isPGroup 2 Z,rfl⟩
  have hj := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple hG T hJ).component
    N ⟨hN,sup_le hJN hTN⟩
  have hnot : ¬ Group.IsSolvable (K.subgroupOf N) := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable hK
      (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hKN).toMonoidHom)
        (subgroupOfEquivOfLe hKN).surjective)
  have hh := cComponent_le_normalizer_of_unique hj (comap_mono hKJ)
    (fun D hD hKD => Chapter1.Section02.IndexTwo.cComponent_unique_over_nonsolvable
      hnot hD hj hKD (comap_mono hKJ))
    (S := (normalizer (K : Set G)).subgroupOf N)
    (by
      change (normalizer (K : Set G)).subgroupOf N ≤ normalizer (K.subgroupOf N : Set N)
      rw [←subgroupOf_normalizer_eq hKN])
  rw [←subgroupOf_normalizer_eq hJN] at hh
  intro x hx
  exact hh (show (⟨x,hNN hx⟩ : N) ∈ (normalizer (K : Set G)).subgroupOf N from hx)

/-- Every maximal local overcomponent of the actual short G₂ factor has
exactly its two-core, including over the field of order four. -/
theorem Preparation.g2_maximal_overcomponent_core
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
      normalizer (residual H : Set G) ≤ normalizer (J : Set G) := by
  have hTH := hH.1.1.2
  obtain ⟨hF,_,⟨a⟩,hb,hs⟩ := d.g2_local_structure h hTH hp F he
  have hK := residual_binary_mem_local hH.1.1 hp h.exponent hb
  let K := residual H
  let R := J.pCoreIn 2
  let Q := K.pCoreIn 2
  have hcore := residual_core_eq_of_sourceS_le h.sylow_normalizes hTH (hs 1)
  have hHJ : H ≤ J ⊔ (T : Subgroup G) := by
    rw [← residual_sup_sylow T H hTH]
    exact sup_le_sup hKJ le_rfl
  have hRQ : R ≤ Q :=
    (pCoreAmbient_mono_of_isSubnormalIn J (J ⊔ (T : Subgroup G)) 2
      le_sup_left hJ.1.1.subnormal).trans
        ((Chapter3.twoCore_le_of_sylow_le T hTH hHJ).trans_eq hcore)
  have hchar := Chapter1.mem_He_iff.mpr
    (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T (h.qtke.evenCharacteristic T) hJ.1)
  change J ⊓ centralizer (R : Set G) ≤ R at hchar
  have hRne : R ≠ ⊥ := by
    intro hr
    have hz : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)
    rw [hr,hz,inf_top_eq] at hchar
    exact d.right_outside (hKJ.trans (hchar.trans bot_le))
  have homega := overcomponent_omega_center a hKJ hchar hRQ
  have hNK := hTH.trans (le_normalizer_residual H)
  have hNJ := maximal_normalizes_of_omega_center h.qtke hK hNK hJ hKJ hRne homega
  refine ⟨?_,hNJ⟩
  rcases he with he | he
  · exact (d.not_g2_short_left_parabolic h hTH hp (he.map fun e => e.left)).elim
  obtain ⟨e⟩ := he
  let P := ChapterF.Source.parabolic ![L,K] (sourceS L H) 1
  have hKP : K ≤ P := le_sup_left.trans le_sup_left
  have hRP : R ≤ P := hRQ.trans ((map_subtype_le _).trans hKP)
  have hPNK : P ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKP).mp
      ((d.hypothesisF11 h hTH).local_normal_in_parabolic 1)
  have hPNR : P ≤ normalizer (R : Set G) := (hPNK.trans hNJ).trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  let N := R.subgroupOf P
  have hn : N.Normal := normal_subgroupOf_of_le_normalizer hPNR
  have hN : N ≤ pCore 2 P := by
    have hh := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J) hRP hPNR
    intro x hx
    exact (mem_map_iff_mem P.subtype_injective).mp (hh hx)
  let N' := N.map e.right.toMonoidHom
  let : N'.Normal := Normal.map hn e.right.toMonoidHom e.right.surjective
  have hN' : N' ≤ pCore 2 (parabolic₁ (F := F)) := by
    rw [←pCore_map_iso 2 e.right]
    exact map_mono hN
  rcases G2Short.core_dichotomy N' hN' with hz | ht
  · have hh : ⁅N,solvableResidual P⁆ = ⊥ := by
      apply map_injective (f := e.right.toMonoidHom) e.right.injective
      rw [map_commutator,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective,Subgroup.map_bot]
      exact hz
    have hhG := congrArg (Subgroup.map P.subtype) hh
    rw [map_commutator,map_subgroupOf_eq_of_le hRP,d.parabolic_residuals h hTH hp 1,Subgroup.map_bot] at hhG
    have hKR : K ≤ R := by
      intro k hk
      exact hchar ⟨hKJ hk,(le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hhG)) hk⟩
    let := hp
    let : Nontrivial K := (nontrivial_iff_ne_bot K).mpr
      (fun he => d.right_outside (show K ≤ normalizer (L : Set G) from he ▸ bot_le))
    exact (Group.IsPerfect.not_isNilpotent K
      ((isPGroup_pCoreIn 2 J).to_le hKR).isNilpotent).elim
  · have hh : N = pCore 2 P := by
      apply map_injective (f := e.right.toMonoidHom) e.right.injective
      rw [pCore_map_iso]
      exact ht
    have heq : R = P.pCoreIn 2 := by
      have hhG := congrArg (Subgroup.map P.subtype) hh
      rwa [map_subgroupOf_eq_of_le hRP] at hhG
    apply le_antisymm hRQ
    rw [heq]
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 K)
      ((map_subtype_le _).trans hKP)
      (hPNK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))


open scoped commutatorElement
/-- The G₂ maximality alternative has no nonnormal-core branch. At field
four it retains the actual overcomponent quotient and the same cubic from
the whole original overlap. -/
theorem Preparation.g2_maximal_or_four_shortlist
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      n = 2 ∧ Nat.card F = 4 ∧ ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
        residual H < J ∧
        J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
          ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist (J ⧸ pCore 2 J) ∧
          ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
              ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ∧
            orderOf x = 3 ∧ x ∈ normalizer (J : Set G) ∧
            (∀ k ∈ residual H, ⁅x,k⁆ ∈ (residual H).pCoreIn 2) ∧
            (∀ q ∈ J.pCoreIn 2, Commute x q → q = 1) ∧
            ⁅J.pCoreIn 2,zpowers x⁆ = J.pCoreIn 2 := by
  rcases d.g2_maximal_or_four_obstruction h hH hp F he with hm | ⟨hn,hF,J,hJ,hKJ,hcase⟩
  · exact .inl hm
  refine .inr ⟨hn,hF,J,hJ,hKJ,?_⟩
  rcases hcase with hnQ | hh
  · have hc := (d.g2_maximal_overcomponent_core h hH hp F he hJ hKJ.le).1
    exact (hnQ (hc ▸ J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))).elim
  · exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

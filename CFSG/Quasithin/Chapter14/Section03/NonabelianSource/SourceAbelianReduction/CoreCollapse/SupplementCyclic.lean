module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.UFixerReflections
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.SupplementOrder
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FactorConjugacySolvable

/-!
# Cyclicity of the original centralizing supplement

A point-aligned split isomorphism sends the actual first elementary factor to
translations and the second factor into the distinguished point centralizer.
The marked quaternion-core fixer has two reflection classes: its tail kernel
fixes the first factor, and every involution in the other coset fixes the
second. Transporting this calculation through the actual conjugation action
and using both self-centralization hypotheses puts every involution of D in
K intersect D = Z. The already proved order four and Z < D force D cyclic.

Source: Aschbacher–Smith 14.3.22, printed p.998. The theorem retains exactly
the source context of `source_supplement_card_four`; no additional action,
fusion or TI premise is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse
open BinaryPermutation.SixNaturalSplit
open Recognition
variable {G : Type*} [Group G] [Finite G]

/-- The actual conjugation action excludes both order-two reflection classes. -/
private theorem cyclic_of_marked_reflection_factors (A B U K D Z : Subgroup G)
    (hAK : A≤K) (hBK : B≤K) (hBA : ¬ B≤A)
    (hselfA : A=centralizer (A:Set G)) (hselfB : B=centralizer (B:Set G))
    (hexp : ∀b∈B,b^2=1)
    (f : K≃*Model) (hfA : (A.subgroupOf K).map f.toMonoidHom=translations)
    (hfU : (U.subgroupOf K).map f.toMonoidHom=canonicalCore)
    (hfB : ∀ b : K, (b:G)∈B → f b∈pointCentralizer)
    (j : D→*fixingSubgroup (MulAut K) (U.subgroupOf K:Set K))
    (hact : ∀d : D, ∀k : K, ((j d:MulAut K) k:G)=(d:G)*(k:G)*(d:G)⁻¹)
    (hKD : K⊓D=Z) (hproper : Z<D) (hc : Nat.card D=4) : IsCyclic D := by
  let B' := (B.subgroupOf K).map f.toMonoidHom
  have hp : B'≤pointCentralizer := by
    rintro _ ⟨b,hb,rfl⟩
    exact hfB b hb
  have he : ∀b∈B',b^2=1 := by
    rintro _ ⟨b,hb,rfl⟩
    have hh : b^2=1 := Subtype.ext (hexp b hb)
    change (f b)^2=1
    rw [←map_pow,hh,map_one]
  have hout : ¬ B'≤translations := by
    intro hh
    apply hBA
    intro b hb
    have hf : f ⟨b,hBK hb⟩∈translations := hh (mem_map_of_mem _ hb)
    rw [←hfA] at hf
    obtain ⟨a,ha,haf⟩ := hf
    have hab : a=(⟨b,hBK hb⟩:K) := f.injective haf
    have habG : (a:G)=b := congrArg Subtype.val hab
    exact habG ▸ ha
  let k : D→*MulAut Model := (MulAut.congr f).toMonoidHom.comp
    ((fixingSubgroup (MulAut K) (U.subgroupOf K:Set K)).subtype.comp j)
  have hk (d : D) : k d∈canonicalFixer := by
    have hm := mem_map_of_mem (MulAut.congr f).toMonoidHom (j d).property
    rw [MulAut.map_fixingSubgroup_congr,hfU] at hm
    exact hm
  have hfix (d : D) (C : Subgroup G) (hCK : C≤K)
      (hfix : k d∈fixingSubgroup (MulAut Model)
        ((C.subgroupOf K).map f.toMonoidHom:Set Model)) :
      (d:G)∈centralizer (C:Set G) := by
    intro c hc
    have hh := ((mem_fixingSubgroup_iff (MulAut Model)).mp hfix) (f ⟨c,hCK hc⟩) (mem_map_of_mem _ hc)
    change f ((j d:MulAut K) (f.symm (f ⟨c,hCK hc⟩)))=f ⟨c,hCK hc⟩ at hh
    rw [f.symm_apply_apply] at hh
    have hv := congrArg (fun a:K=>(a:G)) (f.injective hh)
    rw [hact] at hv
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm
  have htwo (d : D) (hd : d^2=1) : (d:G)∈Z := by
    have hd' : (k d)^2=1 := by rw [←map_pow,hd,map_one]
    have hr := canonicalFixer_square_one_fixes_factor natural_block_normalizer B' hp he hout
      (k d) (hk d) hd'
    have hdK : (d:G)∈K := by
      rcases hr with ha|hb
      · rw [←hfA] at ha
        exact hAK (hselfA ▸ hfix d A hAK ha)
      · exact hBK (hselfB ▸ hfix d B hBK hb)
    rw [←hKD]
    exact ⟨hdK,d.property⟩
  obtain ⟨d,hdD,hdZ⟩ := Set.exists_of_ssubset hproper
  let d' : D := ⟨d,hdD⟩
  have hsq : d'^2≠1 := fun hd=>hdZ (htwo d' hd)
  have hdvd : orderOf d'∣4 := hc ▸ orderOf_dvd_natCard d'
  obtain ⟨n,hn,heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show orderOf d'∣2^2 from hdvd)
  have hord : orderOf d'=4 := by
    interval_cases n
    · have hh : d'=1 := orderOf_eq_one_iff.mp heq
      exact False.elim (hsq (by simp [hh]))
    · exact False.elim (hsq (by simpa only [heq,pow_one] using pow_orderOf_eq_one d'))
    · exact heq
  exact isCyclic_of_orderOf_eq_card d' (hord.trans hc.symm)


open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The original proper supplement is cyclic, excluding both marked reflection classes. -/
theorem source_supplement_cyclic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hproper : F.Vi 1 < F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) :
    IsCyclic (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) : Subgroup G) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨A,B,t,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hAB,hRc,hAN,hBN,hmax,htT,htR,ht⟩ :=
    source_conjugate_maximal_elementary_factors_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let := hEA
  let := hEB
  obtain ⟨hc8,hc8B⟩ := elementary_factor_core_intersections_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
    A B hAR hBR hVA hVB hEA hEB hmax
  let N := F.H⊓normalizer (A:Set G)
  let Y := (pResidual 2 N).map N.subtype
  let K := sourceResidual M Mc⊔Y
  let D := F.H.pCoreIn 2⊓centralizer (F.U:Set G)
  have hRU : (F.I₂ (sourceResidual M Mc)).pCoreIn 2⊔F.U≤K :=
    (factor_generated_residual_geometry_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).2.2.1
  have hBK : B≤K := hBR.trans (le_sup_left.trans hRU)
  obtain ⟨hAK,qA,eK,_,heA⟩ := factor_block_split_model_of_full_orthogonal
    hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hBA : ¬B≤A := by
    intro hh
    have heq : (F.I₂ (sourceResidual M Mc)).pCoreIn 2=A := hAB.symm.trans (sup_eq_left.mpr hh)
    rw [heq,hAc] at hRc
    contradiction
  have hzcard : Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by decide)
  obtain ⟨z,hzne,_⟩ := (Nat.card_eq_two_iff' (1:F.Vi 1)).mp hzcard
  have hzA : (z:G)∈A := hVA (F.le_seed 1 z.property)
  let zK : K := ⟨z,hAK hzA⟩
  have hzK : zK≠1 := fun he=>hzne (Subtype.ext (congrArg (fun a:K=>(a:G)) he))
  have hcore : pointCentralizerTwoResidualCore zK=F.U.subgroupOf K :=
    factor_block_intrinsic_U_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr
      A hAR hVA hAc hc8 hAN zK z.property hzK
  obtain ⟨f,hfA,hfz,hfU⟩ := exists_point_core_aligned_equiv
    (A.subgroupOf K) (F.U.subgroupOf K) eK heA zK hzA hzK hcore.symm
  have hRT : (F.I₂ (sourceResidual M Mc)).pCoreIn 2≤(T:Subgroup G) :=
    (parabolic_core_sylow_index_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr).1
  have hBH : B≤F.H := hBR.trans (hRT.trans (F.invariant 1))
  have hfB : ∀b:K,(b:G)∈B→f b∈pointCentralizer := by
    intro b hb
    have hbc := normalizer_le_centralizer_of_card_two (F.Vi 1) hzcard (hBH hb)
    have hcomm := hbc (z:G) z.property
    have hcommK : zK*b=b*zK := Subtype.ext hcomm
    rw [pointCentralizer_eq,mem_centralizer_singleton_iff]
    change f b * SemidirectProduct.inl (Multiplicative.ofAdd
      (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5)) =
      SemidirectProduct.inl (Multiplicative.ofAdd
      (Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry.pairVector 4 5)) * f b
    simpa only [map_mul,hfz] using (congrArg f hcommK).symm
  obtain ⟨f₀,hf₀A,hf₀U,j,hj,hact,hdihedral,hbound⟩ :=
    factor_block_supplement_action_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN
  have hKD : K⊓D=F.Vi 1 :=
    (factor_block_supplement_index_of_full_orthogonal
      hG T hempty hM hu hmany hcard e hnot F dg hZ hne g hgP hgH hr A hAR hVA hAc hc8 hAN).1
  exact cyclic_of_marked_reflection_factors A B F.U K D (F.Vi 1) hAK hBK hBA
    (hself A hEA hAR hVA hAc hc8 hAN) (hself B hEB hBR hVB hBc hc8B hBN)
    (fun b hb=>elemPow_eq_one_of_isElementaryAbelian b hb) f hfA hfU hfB j hact hKD hproper
    (source_supplement_card_four hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse

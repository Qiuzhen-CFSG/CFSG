module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLineNatural
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoKernelLines
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoKernelRows
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoKernelSpan
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoShearSaturation
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticQuarticCore

/-!
# Removing the remaining strong line-cost row

The strong middle row has an actual whole natural canonical action. Its
original normal-closure kernel again produces every shear into D: the
unchanged support involution gives the required central-cover bound even
though the denominator now meets each marked plane in a line. A moving
cubic plane stabilizer corrects to the literal seed normalizer and contradicts
original Thompson control. The remaining original actor has equal rank and
fixed codimension, one or two.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem PreparedChosenModule.line_natural_false
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      ¬ V ≤ Mc.pCoreIn 2 →
      ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
        (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
        Nat.card (D ⊓ Z₁ : Subgroup G) = 2 →
        Module.finrank (ZMod 2) (dF.imageSpace E) = 2 →
        ∀ n : ℕ, 3 ≤ n →
        ActionEquiv (Representation.BinaryOffender.imageRepresentation ρ)
          (linearNatural BinaryField.two n) →
        let N := normalClosure (V.subgroupOf Mc : Set Mc)
        let L := ((solvableResidual N).map N.subtype).map Mc.subtype
        ⁅F,L⁆ = F → F ≤ L → actionSubgroup ρ (L.subgroupOf Mc) = ⊤ → False := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  dsimp only
  intro hVQ W _ _ ρ dF hline hdimP n hn e hmoved hFL himage
  let : Finite W := Finite.of_surjective (fun x : F => (dF.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp dF.onto)
  let N := normalClosure (V.subgroupOf Mc : Set Mc)
  let H := N.map Mc.subtype
  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let B := K ⊓ H
  have hHMc : H ≤ Mc := map_subtype_le N
  have hLH : L ≤ H := map_mono (map_subtype_le (solvableResidual N))
  have hFH : F ≤ H := hFL.trans hLH
  obtain ⟨_,_,hDC,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hUE := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le (hUE.trans inf_le_left))).trans (localModule_centralizer_le_partner T Mc hu)
  have hNmap : H = conjugateSpanBy V Mc := by
    change N.map Mc.subtype = conjugateSpanBy V Mc
    rw [map_normalClosure_eq_conjugateSpanBy_range,
      map_subgroupOf_eq_of_le hVMc,range_subtype]
  have hHD : H ≤ centralizer (D : Set G) := hNmap ▸
    conjugateSpanBy_le (le_centralizer_iff.mp hDC)
      (hnD.trans (normalizer_le_normalizer_centralizer D))
  have hBD : ⁅B,F⁆ ≤ D := (commutator_mono inf_le_left le_rfl).trans
    (commutator_commutatorPreimage_le Mc F D hnD)
  let : IsElementaryAbelian 2 F := (h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2.2.1
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le dF.kernel_le
  have hmoveH : ⁅F,H⁆ = F := le_antisymm
    (le_normalizer_iff_commutator_le_left.mp (hHMc.trans dF.normalized))
    (hmoved.ge.trans (commutator_mono le_rfl hLH))
  let f := Representation.BinaryOffender.actionHom ρ
  let q := e.groupEquiv.toMonoidHom.comp (f.comp (inclusion hHMc))
  have hqsurj : Function.Surjective q := by
    intro x
    have hx : e.groupEquiv.symm x ∈ actionSubgroup ρ (L.subgroupOf Mc) := himage ▸ mem_top _
    obtain ⟨l,hl,he⟩ := hx
    exact ⟨⟨l,hLH hl⟩,(congrArg e.groupEquiv he).trans (e.groupEquiv.apply_symm_apply x)⟩
  let dNat : BinaryConjugationSection H F D ((specialLinearNatural n).comp q) := {
    section_le := hFH
    kernel_le := dF.kernel_le
    normalized := hHMc.trans dF.normalized
    coordinates := e.linearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp dF.coordinates
    onto := e.linearEquiv.toAddEquiv.toMultiplicative.surjective.comp dF.onto
    kernel_eq := by
      ext x
      change e.linearEquiv (dF.coordinates x).toAdd = 0 ↔ (x:G) ∈ D
      rw [e.linearEquiv.map_eq_zero_iff]
      exact dF.coordinates_eq_one_iff x
    equivariant := by
      intro a x
      change e.linearEquiv (dF.coordinates _).toAdd =
        specialLinearNatural n (q a) (e.linearEquiv (dF.coordinates x).toAdd)
      exact (congrArg e.linearEquiv (dF.equivariant (inclusion hHMc a) x)).trans
        (e.intertwines (f (inclusion hHMc a)) _) }
  have hk (a : H) (ha : q a = 1) : (a:G) ∈ B := by
    refine ⟨?_,a.property⟩
    have hf : f (inclusion hHMc a) = 1 := e.groupEquiv.injective
      (ha.trans e.groupEquiv.map_one.symm)
    have hker : inclusion hHMc a ∈ ρ.ker :=
      congrArg (fun x : Representation.BinaryOffender.actionImage ρ => (x.val).val) hf
    have hh := mem_map_of_mem Mc.subtype hker
    rw [dF.action_kernel_map hnD] at hh
    exact hh
  obtain ⟨hoff,_,_,_,_,_,hsup,_,_,_,_⟩ :=
    ((h.decomposable_five_partner_two_line_actor_bounds hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ) ρ dF hline
  have hex : ∃ i : d.Index, actionSubgroup ρ
      ((plane V (c.ambientFactor d i).space).subgroupOf Mc) ≠ ⊥ := by
    by_contra hh
    push Not at hh
    have hhA := hsup
    rw [hh s.first,hh s.second,bot_sup_eq] at hhA
    exact hoff.1.1 hhA.symm
  obtain ⟨i,hi⟩ := hex
  let A := plane V (c.ambientFactor d i).space
  have hVH : V ≤ H := by
    intro v hv
    exact mem_map_of_mem Mc.subtype
      (subset_normalClosure (show (⟨v,hVMc hv⟩ : Mc) ∈ V.subgroupOf Mc from hv))
  have hAH : A ≤ H := (plane_le _).trans hVH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (plane_le _)
  have hne : ∃ a : A, q (inclusion hAH a) ≠ 1 := by
    obtain ⟨x,hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hi
    obtain ⟨a,ha,he⟩ := x.property
    refine ⟨⟨a,ha⟩,?_⟩
    intro hh
    have hf : f a = 1 := e.groupEquiv.injective (hh.trans e.groupEquiv.map_one.symm)
    exact hxne (Subtype.ext (he.symm.trans hf))
  obtain ⟨_,hFQZ,hEF,_,_,_⟩ := (h.decomposable_five_partner_core_alternatives
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).resolve_left hVQ
  obtain ⟨_,hcore,hQT,_,_,_,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hFT : F ≤ (T : Subgroup G) := hFQZ.trans inf_le_left |>.trans (hcore ▸ hQT)
  have hFE : F ≤ centralizer (E : Set G) := hFQZ.trans inf_le_right |>.trans
    (centralizer_le (hEF.trans (hFQZ.trans inf_le_left)))
  have hFN₁ : F ≤ normalizer (plane V (c.ambientFactor d s.first).space : Set G) :=
    fun x hx => s.centralizer_le_stabilizer ⟨hFT hx,
      (hFE.trans (centralizer_le (show thompsonPlane T V
        (c.ambientFactor d s.first).space ≤ E from inf_le_right))) hx⟩
  have hFN : F ≤ normalizer (A : Set G) := by
    rcases s.covers i with hi | hi
    · simpa only [A,hi] using hFN₁
    · intro x hx
      simpa only [A,hi] using s.stabilizes_second ⟨hFT hx,hFN₁ hx⟩
  have hindex : (centralizer (A : Set G)).relIndex F ≤ 2 :=
    elementary_support_action_index hM.1.2 h.normalized c d s π hp hs hfive F hFT i hFN
  have hBF : ⁅B,F⁆ = D := kernel_span_of_natural_cover H F D B A n hn
    q hqsurj dNat hHD hmoveH hBD hk hAH hne hindex
  obtain ⟨row,heval,_,heqv,hgen⟩ := exists_central_section_rows
    Mc F D H B ρ dF hHMc (inf_le_right.trans hHD) hHD hBD
  have hMcK : Mc ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized Mc F D Mc hnD Mc.le_normalizer dF.normalized hnD
  have hHH : H ≤ normalizer (H : Set G) := H.le_normalizer
  have hHB : H ≤ normalizer (B : Set G) :=
    (le_inf (hHMc.trans hMcK) hHH).trans inf_normalizer_le_normalizer_inf
  let ψ := ρ.comp (inclusion hHMc)
  obtain ⟨hsat,_⟩ := DecomposableQuinticControl.rows_comparison_of_natural_action
    B B H D le_rfl hHB (le_normalizer_iff_commutator_le_right.mp hHB)
    ψ n (by omega) q hqsurj e.linearEquiv
    (fun a w => e.intertwines (f (inclusion hHMc a)) w) row heqv
  have hrow : Function.Surjective row := by
    intro r
    apply (hsat r).mpr
    intro x hx
    have hx' : (x : G) ∈ (⨆ b : B, (row b).range).map D.subtype := by
      rw [hgen,hBF]
      exact x.property
    obtain ⟨y,hy,he⟩ := hx'
    exact D.subtype_injective he ▸ hy
  let P := dF.imageSpace E
  let P' := P.map e.linearEquiv.toLinearMap
  have hdimP' : Module.finrank (ZMod 2) P' = 2 := by
    simpa only [P',LinearEquiv.finrank_map_eq] using hdimP
  obtain ⟨a,ha,haP,w,hw,hwa⟩ :=
    DecomposableQuinticControl.exists_order_three_moving_subspace n P' (Or.inl hdimP')
  obtain ⟨g,hga⟩ := hqsurj a
  let g₀ := inclusion hHMc g
  have hcube : ρ (g₀^3) = 1 := by
    have he : f (g₀^3) = 1 := e.groupEquiv.injective (by
      rw [map_one,map_pow,map_pow]
      change q g ^ 3 = 1
      rw [hga]
      exact ha ▸ pow_orderOf_eq_one a)
    change Representation.BinaryOffender.imageRepresentation ρ (f (g₀^3)) = 1
    rw [he,map_one]
  have hgP : g₀ ∈ subspaceStabilizer ρ P := by
    change f g₀ ∈ subspaceStabilizer (Representation.BinaryOffender.imageRepresentation ρ) P
    apply (mem_subspaceStabilizer_equivariant _ (linearNatural BinaryField.two n)
      e.groupEquiv e.linearEquiv e.intertwines P (f g₀)).mpr
    change q g ∈ _
    rw [hga]
    exact (subspace_map_eq_iff (linearNatural BinaryField.two n) P' a).mp haP
  obtain ⟨v,hv,hvw⟩ := hw
  have hgv : ρ g₀ v ≠ v := by
    intro hvv
    apply hwa
    have hh := e.intertwines (f g₀) v
    change e.linearEquiv (ρ g₀ v) = specialLinearNatural n (q g) (e.linearEquiv v) at hh
    rw [hvv,hga] at hh
    rw [←hvw]
    exact hh.symm
  have hBMc : B ≤ Mc := inf_le_right.trans hHMc
  obtain ⟨b,hbn,hbe⟩ := DecomposableQuinticControl.exists_row_correction_normalizing_subgroup
    Mc F D E B ρ dF (le_conjugateSpanBy E C) hBMc row hrow heval g₀ (hHD g.property)
    ((subspace_map_eq_iff ρ P g₀).mpr hgP)
  let g' := inclusion hBMc b * g₀
  have hcube' : ρ (g'^3) = 1 := by rw [map_pow,hbe,←map_pow,hcube]
  have hfixed := h.decomposable_five_partner_two_normalizer_cubic_fixed
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU ρ dF g' hbn hcube'
  exact hgv (hbe ▸ hfixed v hv)

/- The strong line row is excluded on the original source. -/
theorem PreparedChosenModule.decomposable_five_partner_two_core_or_equal_cost
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (_dF : BinaryConjugationSection Mc F D ρ),
          let σ := Representation.BinaryOffender.imageRepresentation ρ
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          (rank A = 1 ∨ rank A = 2) ∧ fixedCodim σ A = rank A ∧ ¬IsStrongOffender σ A := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF
  have hline := ((h.decomposable_five_partner_two_core_or_kernel_lines
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ).1
  obtain ⟨_,_,_,_,_,_,_,hcases⟩ :=
    ((h.decomposable_five_partner_two_line_natural_or_equal_cost
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hline
  rcases hcases with hlow | hstrong | hhigh
  · obtain ⟨hr,hcost,_⟩ := hlow
    exact ⟨Or.inl hr,hcost.trans hr.symm,fun hh => by have hlt := hh.2; omega⟩
  · obtain ⟨_,_,hdim,_,_,_,_,n,hn,⟨e⟩,_,_,_,_,_,hm,hFL,himage⟩ := hstrong
    exact (h.line_natural_false hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq
      hfive hcU hVQ ρ dF hline hdim n (by rcases hn with rfl|rfl|rfl <;> decide)
      e hm hFL himage).elim
  · obtain ⟨hr,hcost,_,_,hn⟩ := hhigh
    exact ⟨Or.inr hr,hcost.trans hr.symm,hn⟩

end CFSG.Quasithin.Chapter15.Section01

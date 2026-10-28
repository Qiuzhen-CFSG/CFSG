module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedLinearReturn
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.FixedLineKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.LinearSocleCases
public import Theory.Representation.PSL3Two.DualLineRadical
public import Theory.Representation.PSL3Two.SmallModuleProperties

/-!
# Excluding the mixed dual-natural constituents

In a noncommuting mixed pair the original conjugator returns to L₂T,
so the same V₀ normalizes V. In either the semisimple natural-plus-dual
model or the point-core model, take the actual image of the faithful
three-dimensional dual constituent. Its displacement by V lies in
C_{V₀}(L₂T) ≤ C_V(L). The original fixed-line kernel makes that constituent
centralize V. Faithfulness then forces V to centralize all of V₀,
contradicting the mixed hypothesis.

The source application selects the original whole-module marking and
excludes both models. The only remaining linear row is the permutation
core whose fixed line is outside its socle; the existing model calculation
therefore gives weight four and noncontainment in the opposite residual
commutator. The remaining weight-four block contradiction, product case,
and graph argument are separate obligations. All original earlier-source
and normalizer-fusion inputs are retained.

Source: Aschbacher–Smith 13.4.14–15, printed pp.911–912,
refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem restricted_core_image (B C : Subgroup G)
    (f : C →* BinaryLinearThree.Group) (hk : IsPGroup 2 f.ker)
    (hB : (B.subgroupOf C).map f = Matrix.PSL3Two.lineParabolicSL) :
    ((B.pCoreIn 2).subgroupOf C).map f ≤ Matrix.PSL3Two.lineParabolicSL.pCoreIn 2 := by
  rw [←hB,←map_pCoreIn_of_ker_isPGroup f hk]
  apply map_mono
  apply (map_le_map_iff_of_injective C.subtype_injective).mp
  rw [subgroupOf_map_subtype,map_pCoreIn_of_injective 2 _ C.subtype C.subtype_injective,subgroupOf_map_subtype]
  intro x hx
  exact inf_pCoreIn_le_of_le 2 (show B ⊓ C ≤ B from inf_le_left)
    ⟨⟨pCoreIn_le 2 B hx.1,hx.2⟩,hx.1⟩

private theorem dual_constituent_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (U C B : Subgroup G) [IsElementaryAbelian 2 U]
    (hCU : C ≤ normalizer (U : Set G))
    (f : C →* BinaryLinearThree.Group) (hk : IsPGroup 2 f.ker)
    (M : Type*) [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
    (E : Representation.Equiv (σ.comp f) (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hCU))))
    (j : BinaryLinearThree.W.dual.IntertwiningMap σ) (hj : Function.Injective j)
    (hB : (B.subgroupOf C).map f = Matrix.PSL3Two.lineParabolicSL)
    (hrepB : ∀ b ∈ B, ∃ c : C, c.val ∈ B ∧ ∀ u : U,
      b*u.val*b⁻¹ = c.val*u.val*c.val⁻¹)
    (hrepR : ∀ b ∈ B.pCoreIn 2, ∃ c : C, c.val ∈ B.pCoreIn 2 ∧ ∀ u : U,
      b*u.val*b⁻¹ = c.val*u.val*c.val⁻¹)
    (hUV : U ≤ normalizer (V : Set G)) (hVR : V ≤ B.pCoreIn 2)
    (hfixed : U ⊓ centralizer (B : Set G) ≤ V ⊓ centralizer (L : Set G)) :
    ⁅V,U⁆ = ⊥ := by
  let J := (binarySubgroup (LinearMap.range (E.toLinearMap.comp j.toLinearMap))).map U.subtype
  have hJU : J ≤ U := map_subtype_le _
  have jmem (w : Module.Dual (ZMod 2) BinaryLinearThree.Vector) :
      (E (j w)).toMul.val ∈ J := mem_map_of_mem U.subtype ⟨w,rfl⟩
  have he (c : C) (w : M) :
      (E (σ (f c) w)).toMul.val = c.val*(E w).toMul.val*c.val⁻¹ :=
    congrArg (fun a : Additive U => a.toMul.val)
      (LinearMap.congr_fun (E.isIntertwining' c) w)
  have hcomm : ⁅J,V⁆ ≤ V ⊓ centralizer (L : Set G) := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro v hv a ha
    obtain ⟨a,ha,rfl⟩ := ha
    obtain ⟨w,hw⟩ := ha
    change E (j w) = Additive.ofMul a at hw
    obtain ⟨c,hc,hcv⟩ := hrepR v (hVR hv)
    have hr : f c ∈ Matrix.PSL3Two.lineParabolicSL.pCoreIn 2 :=
      restricted_core_image B C f hk hB (mem_map_of_mem f hc)
    have hd := BinaryLinearThree.dual_line_radical_displacement (f c) hr w
    have hdj : j (BinaryLinearThree.W.dual (f c) w - w) ∈
        fixedSpace σ Matrix.PSL3Two.lineParabolicSL := by
      intro b
      exact (LinearMap.congr_fun (j.isIntertwining' b.val) _).symm.trans
        (congrArg j (hd b))
    rw [←hB,←modelSpace_fixed U C hCU f σ E B hrepB] at hdj
    have hdisp : (E (j (BinaryLinearThree.W.dual (f c) w - w))).toMul.val ∈
        V ⊓ centralizer (L : Set G) := hfixed hdj
    rw [map_sub,map_sub] at hdisp
    have hje : j (BinaryLinearThree.W.dual (f c) w) = σ (f c) (j w) :=
      LinearMap.congr_fun (j.isIntertwining' (f c)) w
    rw [hje] at hdisp
    change (E (σ (f c) (j w))).toMul.val / (E (j w)).toMul.val ∈ _ at hdisp
    rw [div_eq_mul_inv] at hdisp
    rw [he,hw] at hdisp
    change c.val*a.val*c.val⁻¹*a.val⁻¹ ∈ _ at hdisp
    rw [←hcv a] at hdisp
    exact hdisp
  have hzero : ⁅V,J⁆ = ⊥ := original_fixed_line_kernel h structural D m J
    (hJU.trans hUV) (by rwa [commutator_comm])
  have hJV : J ≤ centralizer (V : Set G) := by
    rw [commutator_comm] at hzero
    exact commutator_eq_bot_iff_le_centralizer.mp hzero
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro v hv a ha
  obtain ⟨c,hc,hcv⟩ := hrepR v (hVR hv)
  have hfc : f c = 1 := by
    apply BinaryLinearThree.dual_injective
    apply LinearMap.ext
    intro w
    rw [map_one,Module.End.one_apply]
    apply hj
    apply E.injective
    apply Additive.toMul.injective
    apply Subtype.ext
    have hje : j (BinaryLinearThree.W.dual (f c) w) = σ (f c) (j w) :=
      LinearMap.congr_fun (j.isIntertwining' (f c)) w
    change (E (j (BinaryLinearThree.W.dual (f c) w))).toMul.val = (E (j w)).toMul.val
    rw [hje,he,←hcv (E (j w)).toMul]
    exact mul_inv_eq_iff_eq_mul.mpr (hJV (jmem w) v hv)
  obtain ⟨w,hw⟩ := E.surjective (Additive.ofMul ⟨a,ha⟩)
  have hcfix : c.val*a*c.val⁻¹ = a := by
    have hh := he c w
    rw [hfc,map_one,Module.End.one_apply] at hh
    change E w = _ at hw
    rw [hw] at hh
    exact hh.symm
  exact (mul_inv_eq_iff_eq_mul.mp ((hcv ⟨a,ha⟩).trans hcfix)).symm
open Stellmacher Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

private theorem original_pair_dual_constituent_centralizes
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))
    (q : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hqA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (M : Type*) [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) BinaryLinearThree.Group M)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv (σ.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))))))
    (j : BinaryLinearThree.W.dual.IntertwiningMap σ) (hj : Function.Injective j)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hUV : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) ≤
      normalizer (V : Set G)) :
    ⁅V,conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)⁆ = ⊥ := by
  let := he
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  let C := K.map X.subtype
  let Q := X.pCoreIn 2
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  change (A.subgroupOf C).map f = _ at hqA
  change (B.subgroupOf C).map f = _ at hqB
  change ((T : Subgroup G).subgroupOf C).map f = _ at hqT
  have hUX : U ≤ X := conjugateSpanBy_le_self (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hXU := le_normalizer_conjugateSpanBy Z X
  have hker := Amalgam.original_pair_action_kernel h₀ D m hTA hTB eA eB hne hiA hiB
  have hUT : U ≤ (T : Subgroup G) := by
    have huq : U ≤ Q := by
      intro x hx
      exact mem_map_of_mem X.subtype (hker.1.le_pCore (show (⟨x,hUX hx⟩ : X) ∈ U.subgroupOf X from hx))
    exact huq.trans (hker.2.2.2.symm.le.trans inf_le_left)
  have hQT : Q ≤ (T : Subgroup G) := hker.2.2.2.symm.le.trans inf_le_left
  have hQU : Q ≤ centralizer (U : Set G) := hker.2.2.2.symm.le.trans inf_le_right
  have hgen : C ⊔ Q = X := (Amalgam.original_pair_linear_core_supplement
    h₀ D m h1332 hTA hTB eA eB hne hiA hiB K hK eK).2
  let : (Q.subgroupOf X).Normal := by
    change ((X.pCoreIn 2).subgroupOf X).Normal
    change (((pCore 2 X).map X.subtype).comap X.subtype).Normal
    rw [comap_map_eq_self_of_injective X.subtype_injective]
    infer_instance
  have reps (P : Subgroup G) (hPX : P ≤ X) (hQP : Q ≤ P) :=
    centralizing_supplement_representatives X C Q U P (map_subtype_le K) (pCoreIn_le 2 X)
      hgen hQU hPX hQP
  have hQB : Q ≤ B := hQT.trans hTB
  have hQR : Q ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 X) hQB
    (le_sup_right.trans (X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))))
  have hBM : B ≤ normalizer (L : Set G) := by
    rw [hB]
    exact inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hVR : V ≤ B.pCoreIn 2 := by
    let := D.elementary
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
      (D.le_sylow.trans hTB) (hBM.trans (normalizer_component_le_module h structural D m))
  have hfixed : U ⊓ centralizer (B : Set G) ≤ V ⊓ centralizer (L : Set G) := by
    intro u hu
    have huZ : u ∈ Z := (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hUT hu.1,elemPow_eq_one_of_isElementaryAbelian _ hu.1,centralizer_le hTB hu.2⟩
    have hh := Solvable.original_second_flag_fixed D m W hW hTW
    rw [←hB] at hh
    exact hh ▸ ⟨hZV huZ,centralizer_le (map_subtype_le (pResidual 2 B)) hu.2⟩
  have hfk : f.ker = pCore 2 C := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ q.injective,QuotientGroup.ker_mk']
  exact dual_constituent_centralizes h structural D m U C B
    ((map_subtype_le K).trans hXU) f (hfk ▸ pCore_isPGroup) M σ E j hj hqB
    (reps B le_sup_right hQB)
    (reps (B.pCoreIn 2) ((pCoreIn_le 2 B).trans le_sup_right) hQR) hUV hVR hfixed

/-- Under the literal reciprocal R₂ containments, noncentral mixed action
excludes the semisimple and point-core rows and forces the original
weight-four, fixed-line-outside-socle alternative. -/
theorem original_linear_pair_mixed_weight_four
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G)) :
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z X
    let F := V ⊓ centralizer (L : Set G)
    let R := ⁅Z,(pResidual 2 A).map A.subtype⁆
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ →
      ∃ he : IsElementaryAbelian 2 U, let := he
        let ρ := elementaryRepresentation (p := 2)
          (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z X)))
        let Soc := (sSup {S : Subrepresentation ρ | IsAtom S}).toSubmodule
        Nat.card U = 64 ∧ m.weight z = 4 ∧ ¬ F ≤ R ∧
          ¬ binarySpace (F.subgroupOf U) ≤ Soc := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  dsimp only
  intro g h₁ h₂ hm
  obtain ⟨_,_,hUg,_,_,_,_⟩ := original_linear_pair_mixed_return
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 hlin eL hM hZV W hW hTW hB hfusion g h₁ h₂ hm
  change U.conjBy g = U at hUg
  have hmove : ⁅V,U⁆ ≠ ⊥ := by rwa [hUg] at hm
  have hUM : U ≤ normalizer (V : Set G) := by
    have hUR : U ≤ B.pCoreIn 2 := hUg ▸ h₁
    apply hUR.trans ((pCoreIn_le 2 B).trans ?_)
    rw [hB]
    exact inf_le_left.trans ((sup_le L.le_normalizer D.sylow_normalizes_component).trans
      (normalizer_component_le_module h structural D m))
  obtain ⟨C,hC,_,_,_,_,⟨eC⟩⟩ := hlin.1
  let K := C.subgroupOf X
  have hmap : K.map X.subtype = C := map_subgroupOf_eq_of_le hC.1
  have eK : ((K.map X.subtype) ⧸ pCore 2 (K.map X.subtype)) ≃* Matrix.PSL3Two.PSL :=
    hmap.symm ▸ eC
  obtain ⟨he,q,hqA,hqB,hqT,models,hcard⟩ := Amalgam.original_pair_linear_whole_module
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 K hC.2 eK
  let := he
  have exclude {N : Type} [AddCommGroup N] [Module (ZMod 2) N]
      (σ : Representation (ZMod 2) BinaryLinearThree.Group N)
      (E : Representation.Equiv (σ.comp (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))))
      (j : BinaryLinearThree.W.dual.IntertwiningMap σ) (hj : Function.Injective j) : False :=
    hmove (original_pair_dual_constituent_centralizes h₀ D m h1332 hTA hTB eA eB hne
      hindexA hindexB K hC.2 eK he q hqA hqB hqT N σ E j hj
      h structural hZV W hW hTW hB hUM)
  rcases models with hs | hp | hl
  · let j : BinaryLinearThree.W.dual.IntertwiningMap
        (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) := {
      toLinearMap := LinearMap.inr _ _ _
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro w
        apply Prod.ext
        · exact (map_zero (BinaryLinearThree.W g)).symm
        · rfl }
    exact (exclude _ hs.some j (fun a b he => congrArg Prod.snd he)).elim
  · exact (exclude _ hp.some BinaryLinearThree.FanoDecomposition.pointEvaluation
      BinaryLinearThree.FanoDecomposition.pointEvaluation_injective).elim
  · refine ⟨he,hcard,?_⟩
    exact original_line_core_weight_and_socle h₀ D m h1332 hTA hTB eA eB hne
      hindexA hindexB K hC.2 eK he q hqA hqB hqT hl.some h structural hM hZV
      W hW hTW hB z hzT hzL hAz

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

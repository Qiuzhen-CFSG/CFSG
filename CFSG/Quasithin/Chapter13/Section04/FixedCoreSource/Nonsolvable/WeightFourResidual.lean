module
public import Theory.Representation.BinaryPermutation.SixCoreResidualLine
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.MixedConstituents
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.Representation.BinaryConjugationCoordinates.SupplementSpaces

/-!
# The original weight-four residual three-space

Let L₁=O^{3′}(C_L(z)) for a weight-four vector of the original augmentation
core V. Transporting the literal centralizer action and its two-kernel gives
|[V,L₁]|=8, excludes C_V(L)'s generator from that three-space, and identifies
[[V,L₁],O₂(L₁)] with ⟨z⟩. Relative normality puts [V,L₁] in O₂(L₁), hence
z lies in the derived subgroup of that same two-core.

The subgroup [V,L₁]C_V(L) has order sixteen and its commutator with O₂(L₁)
is again ⟨z⟩. Its containment in O₂(L₁) is proved when C_V(L)≤L₁. This
placement is retained as a premise of that last conditional consequence;
it is not inferred from the local module calculation.

The final theorem applies the calculation to the original noncommuting
mixed pair, using its already proved weight-four reduction. The reciprocal
component's block structure, fixed-line placement and center bound still
remain before the mixed contradiction; product reciprocity, the coset graph
and final offender contradiction also remain with this source owner.
All original hypotheses, quotient maps and prior source inputs are retained.

Source: Aschbacher–Smith 13.4.15, final paragraph, printed p.912,
refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryPermutation Representation.BinaryConjugationCoordinates
open SixCoreResidualLine SixCoreResidualMovement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal first residual moves an eight-group avoiding the fixed line.
Its two-core moves that eight-group exactly onto the original weight-four point. -/
theorem original_weight_four_residual_geometry
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzL : z.val ∉ centralizer (L : Set G)) (hw : m.weight z = 4) :
    let J := Solvable.firstCentralizerResidual L z.val
    Nat.card (⁅V,J⁆ : Subgroup G) = 8 ∧
      m.constant.val ∉ ⁅V,J⁆ ∧ ⁅⁅V,J⁆,J.pCoreIn 2⁆ = zpowers z.val := by
  let := D.elementary
  let C := L ⊓ centralizer ({z.val} : Set G)
  let J := Solvable.firstCentralizerResidual L z.val
  let w := (m.coordinate z).toAdd
  obtain ⟨f,hf,hfk,he⟩ := Solvable.component_centralizer_action D m z
  let q : C →* A := (S w).subtype.comp f
  have hqk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (S w).subtype_injective,hfk,
      Solvable.centralCore_eq_twoCore_of_ordinary eL]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hCV : C ≤ normalizer (V : Set G) := inf_le_left.trans D.normalizes
  let da : Additive V ≃+ W := m.coordinate.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let d : Additive V ≃ₗ[ZMod 2] W := { da with map_smul' := ZMod.map_smul da }
  let E₀ : Representation.Equiv (elementaryRepresentation (p := 2)
      (V.normalizerMonoidHom.comp (inclusion hCV))) (rho.comp q) := {
    toLinearEquiv := d
    isIntertwining' := by
      intro c
      apply LinearMap.ext
      intro v
      exact he c v.toMul }
  let E := E₀.symm
  let space := modelSpace V C hCV q rho E
  have htop : space V = ⊤ := by
    apply top_unique
    intro v _
    exact (E v).toMul.property
  have hJC : J ≤ C := Solvable.firstCentralizerResidual_le L z.val
  have hJN : J ≤ normalizer (V : Set G) := hJC.trans hCV
  have hPV : ⁅V,J⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hJN
  have hJR : (J.subgroupOf C).map q = residual w := by
    change (J.comap C.subtype).map ((S w).subtype.comp f) = _
    rw [show J = (primeToResidual 3 C).map C.subtype from
      Solvable.firstCentralizerResidual_eq L z.val,comap_map_eq_self_of_injective C.subtype_injective,
      ←map_map,map_primeToResidual_of_surjective 3 f hf]
    rfl
  have hQR : ((J.pCoreIn 2).subgroupOf C).map q = (residual w).pCoreIn 2 := by
    rw [←pCoreIn_subgroupOf 2 J C hJC,map_pCoreIn_of_ker_isPGroup q hqk,hJR]
  have hspace : space ⁅V,J⁆ = moved w := by
    have hh := modelSpace_commutator V C hCV q rho E V J le_rfl hJN
      (fun a ha => ⟨⟨a,hJC ha⟩,ha,fun _ => rfl⟩)
    change space ⁅V,J⁆ = subspaceCommutator rho (space V) ((J.subgroupOf C).map q) at hh
    rw [htop,hJR] at hh
    exact hh
  have hdouble : space ⁅⁅V,J⁆,J.pCoreIn 2⁆ =
      subspaceCommutator rho (moved w) ((residual w).pCoreIn 2) := by
    have hh := modelSpace_commutator V C hCV q rho E ⁅V,J⁆ (J.pCoreIn 2) hPV
      ((pCoreIn_le 2 J).trans hJN)
      (fun a ha => ⟨⟨a,hJC (pCoreIn_le 2 J ha)⟩,ha,fun _ => rfl⟩)
    change space ⁅⁅V,J⁆,J.pCoreIn 2⁆ = subspaceCommutator rho (space ⁅V,J⁆)
      (((J.pCoreIn 2).subgroupOf C).map q) at hh
    rwa [hspace,hQR] at hh
  have hmodel := weight_four_residual w hw
  have card_space (P : Subgroup G) (hP : P ≤ V) : Nat.card (space P) = Nat.card P := by
    let eP : space P ≃ P := {
      toFun v := ⟨(E v.val).toMul.val,v.property⟩
      invFun x := ⟨E.symm (Additive.ofMul ⟨x.val,hP x.property⟩),by
        change (E (E.symm _)).toMul.val ∈ P
        rw [E.apply_symm_apply]
        exact x.property⟩
      left_inv v := by apply Subtype.ext; exact E.symm_apply_apply v.val
      right_inv x := by
        apply Subtype.ext
        exact congrArg (fun v : Additive V => v.toMul.val)
          (E.apply_symm_apply (Additive.ofMul ⟨x.val,hP x.property⟩)) }
    exact Nat.card_congr eP
  have hcard : Nat.card (⁅V,J⁆ : Subgroup G) = 8 := by
    rw [←card_space ⁅V,J⁆ hPV,hspace]
    exact hmodel.1
  have hconst : m.constant.val ∉ ⁅V,J⁆ := by
    intro hh
    apply hmodel.2.1
    rw [←hspace]
    exact hh
  have hDV : ⁅⁅V,J⁆,J.pCoreIn 2⁆ ≤ V :=
    (commutator_mono hPV (pCoreIn_le 2 J)).trans hPV
  have hline : ⁅⁅V,J⁆,J.pCoreIn 2⁆ ≤ zpowers z.val := by
    intro x hx
    let v : Additive V := Additive.ofMul ⟨x,hDV hx⟩
    have hsp : E.symm v ∈ space ⁅⁅V,J⁆,J.pCoreIn 2⁆ := by
      change (E (E.symm v)).toMul.val ∈ (⁅⁅V,J⁆,J.pCoreIn 2⁆ : Subgroup G)
      rwa [E.apply_symm_apply]
    rw [hdouble] at hsp
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hmodel.2.2 hsp)
    have hh : x = (E (c • w)).toMul.val := by
      rw [hc,E.apply_symm_apply]
      rfl
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [hh,zero_smul,map_zero]
      exact one_mem _
    · rw [hh,one_smul]
      change (m.coordinate.symm (m.coordinate z)).val ∈ zpowers z.val
      rw [m.coordinate.symm_apply_apply]
      exact mem_zpowers z.val
  have hn : ⁅⁅V,J⁆,J.pCoreIn 2⁆ ≠ ⊥ :=
    Solvable.firstCentralizerResidual_double_commutator_ne_bot D m
      (by rw [Solvable.centralCore_eq_twoCore_of_ordinary eL]; exact pCore_isPGroup) z hzL
  have hz1 : z.val ≠ 1 := fun hh => hzL (hh ▸ one_mem _)
  have horder : orderOf z.val = 2 := by
    exact orderOf_eq_prime_iff.mpr
      ⟨elemPow_eq_one_of_isElementaryAbelian _ z.property,hz1⟩
  have hlinecard : Nat.card (zpowers z.val) = 2 := by rw [Nat.card_zpowers,horder]
  have heq : ⁅⁅V,J⁆,J.pCoreIn 2⁆ = zpowers z.val := by
    apply eq_of_le_of_card_ge hline
    rw [hlinecard]
    have hpos := Nat.card_pos (α := (⁅⁅V,J⁆,J.pCoreIn 2⁆ : Subgroup G))
    have hnot : Nat.card (⁅⁅V,J⁆,J.pCoreIn 2⁆ : Subgroup G) ≠ 1 :=
      fun hh => hn (card_eq_one.mp hh)
    omega
  exact ⟨hcard,hconst,heq⟩

/-- The residual eight-group lies in the literal residual two-core. Adjoining
 the original fixed line gives an elementary sixteen-group; if that line lies
 in the residual, so does the whole sixteen-group, inside the same two-core. -/
theorem original_weight_four_residual_sixteen
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzL : z.val ∉ centralizer (L : Set G)) (hw : m.weight z = 4) :
    let J := Solvable.firstCentralizerResidual L z.val
    let P := ⁅V,J⁆
    let F := V ⊓ centralizer (L : Set G)
    P ≤ J.pCoreIn 2 ∧ z.val ∈ ⁅J.pCoreIn 2,J.pCoreIn 2⁆ ∧
      Nat.card (P ⊔ F : Subgroup G) = 16 ∧
        ⁅P ⊔ F,J.pCoreIn 2⁆ = zpowers z.val ∧ (F ≤ J → P ⊔ F ≤ J.pCoreIn 2) := by
  let := D.elementary
  let C := L ⊓ centralizer ({z.val} : Set G)
  let J := Solvable.firstCentralizerResidual L z.val
  let P := ⁅V,J⁆
  let F := V ⊓ centralizer (L : Set G)
  obtain ⟨hcard,hconst,hcomm⟩ := original_weight_four_residual_geometry D m eL z hzL hw
  have hJL : J ≤ L := (Solvable.firstCentralizerResidual_le L z.val).trans inf_le_left
  have hPV : P ≤ V := le_normalizer_iff_commutator_le_left.mp (hJL.trans D.normalizes)
  have hVC : V ≤ C := le_inf D.le_component (by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨v,hv⟩ : V) z)))
  have hCN : C ≤ normalizer (J : Set G) := by
    change C ≤ normalizer (Solvable.firstCentralizerResidual L z.val : Set G)
    rw [Solvable.firstCentralizerResidual_eq]
    exact C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))
  have hPJ : P ≤ J := le_normalizer_iff_commutator_le_right.mp (hVC.trans hCN)
  have hPQ : P ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).of_injective (inclusion hPV) (inclusion_injective _))
    hPJ (normalizer_commutator_ge_right V J)
  have hz : z.val ∈ ⁅J.pCoreIn 2,J.pCoreIn 2⁆ := by
    apply commutator_mono hPQ le_rfl
    rw [hcomm]
    exact mem_zpowers z.val
  have hFP : F ≤ centralizer (P : Set G) :=
    inf_le_right.trans (centralizer_le (hPJ.trans hJL))
  have hdis : Disjoint P F := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    rcases (m.fixed_iff ⟨x,hx.2.1⟩).mp hx.2.2 with he | he
    · exact congrArg Subtype.val he
    · have hx' : x = m.constant.val := congrArg Subtype.val he
      exact False.elim (hconst (hx' ▸ hx.1))
  have hs : Nat.card (P ⊔ F : Subgroup G) = 16 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint P F
      (hFP.trans (Subgroup.centralizer_le_normalizer _)) hdis,hcard,m.card_fixed]
  have hsum : ⁅P ⊔ F,J.pCoreIn 2⁆ = zpowers z.val := by
    apply le_antisymm
    · apply commutator_le.mpr
      intro x hx q hq
      have hx' : x ∈ (P : Set G) * (F : Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left P F
          (hFP.trans (Subgroup.centralizer_le_normalizer _))]
        exact hx
      obtain ⟨p,hp,f,hf,rfl⟩ := hx'
      have hfc : ⁅f,q⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (hf.2 q (hJL (pCoreIn_le 2 J hq))).symm
      rw [commutatorElement_mul_left_eq_conj_mul,hfc,mul_one,mul_inv_cancel,one_mul]
      exact hcomm.le (commutator_mem_commutator hp hq)
    · exact hcomm.symm.le.trans (commutator_mono le_sup_left le_rfl)
  refine ⟨hPQ,hz,hs,hsum,fun hFJ => sup_le hPQ ?_⟩
  exact le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).of_injective (inclusion (show F ≤ V from inf_le_left))
      (inclusion_injective _)) hFJ
    ((le_centralizer_iff.mp (inf_le_right.trans (centralizer_le hJL))).trans
      (Subgroup.centralizer_le_normalizer _))

open Stellmacher Chapter14.Section03.FaithfulSource Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

/-- The original mixed noncommuting pair supplies the residual three-space,
 its exact nontrivial commutator and the sixteen-group needed for the final
 center comparison. The fixed-line placement in L₁ remains explicit in that
 last containment; no local hypothesis is promoted to a universal input. -/
theorem original_linear_pair_mixed_residual_geometry
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
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    let J := Solvable.firstCentralizerResidual L z.val
    let P := ⁅V,J⁆
    let F := V ⊓ centralizer (L : Set G)
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ ≠ ⊥ →
      m.weight z = 4 ∧ Nat.card P = 8 ∧ m.constant.val ∉ P ∧
        P ≤ J.pCoreIn 2 ∧ ⁅P,J.pCoreIn 2⁆ = zpowers z.val ∧
        z.val ∈ ⁅J.pCoreIn 2,J.pCoreIn 2⁆ ∧ Nat.card (P ⊔ F : Subgroup G) = 16 ∧
        ⁅P ⊔ F,J.pCoreIn 2⁆ = zpowers z.val ∧ (F ≤ J → P ⊔ F ≤ J.pCoreIn 2) := by
  dsimp only
  intro g h₁ h₂ hm
  obtain ⟨_,_,hw,_,_⟩ := original_linear_pair_mixed_weight_four
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 hlin eL hM hZV W hW hTW hB hfusion z hzT hzL hAz g h₁ h₂ hm
  obtain ⟨hc,hn,hd⟩ := original_weight_four_residual_geometry D m eL z hzL hw
  obtain ⟨hp,hz,hcard,hsum,hbound⟩ := original_weight_four_residual_sixteen D m eL z hzL hw
  exact ⟨hw,hc,hn,hp,hd,hz,hcard,hsum,hbound⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

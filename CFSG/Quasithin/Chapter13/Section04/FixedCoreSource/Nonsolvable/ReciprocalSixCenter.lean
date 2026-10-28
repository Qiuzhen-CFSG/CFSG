module
public import Theory.Representation.BinaryPermutation.SixCoreResidualCenter
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalSix
public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The reciprocal A₆ radical center and the mixed-pair contradiction

Let J be the literal cubic residual of a nonfixed augmentation point
centralizer. If E ≤ O₂(J) is central modulo the component's fixed line,
faithfulness on [U,J] puts E in O₂(K). The fixed-space calculation bounds
|E ∩ U| by four, and the perfect central-cover bound gives |E/(E ∩ U)| ≤ 2.
Applied to the preimage of Z(O₂(J)/⟨z⟩), this proves its order is at most four.
This avoids identifying a full extraspecial model and retains central covers.

For the original mixed pair, the existing reciprocal identity identifies
this J with O^{3′}(C_L(z)). Its sixteen-group gives the incompatible lower
bound eight in the SAME quotient. Thus the selected ordinary A₆ branch of
the mixed reciprocal exclusion is proved with the original conjugator and
both radical containments. Earlier-source inputs remain explicit; this does
not assert product reciprocity, point fusion or the final graph argument.
Source: Aschbacher–Smith 13.4.15, printed p.912, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryPermutation Representation.BinaryConjugationCoordinates
open SixCoreResidualMovement SixCoreResidualLine SixCoreResidualCenter
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- In an augmentation A₆ block, a subgroup of the literal point radical
central modulo the fixed line has at most eight elements. -/
theorem core_point_radical_central_mod_fixed_card [Group.IsPerfect K]
    (D : ChosenModule T K U) (m : CoreMarking D)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hU : (ChapterC.blockU K).map K.subtype=U)
    (v : U) (hv : v.val ∉ centralizer (K : Set G))
    (E : Subgroup G) (hE : E ≤ (Solvable.firstCentralizerResidual K v.val).pCoreIn 2)
    (hc : ⁅E,(Solvable.firstCentralizerResidual K v.val).pCoreIn 2⁆ ≤
      U ⊓ centralizer (K : Set G)) : Nat.card E ≤ 8 := by
  let := D.elementary
  let C := K ⊓ centralizer ({v.val} : Set G)
  let J := Solvable.firstCentralizerResidual K v.val
  let Q := J.pCoreIn 2
  let w := (m.coordinate v).toAdd
  obtain ⟨f,hf,hfk,he⟩ := Solvable.component_centralizer_action D m v
  let q : C →* A := (S w).subtype.comp f
  have hqk : q.ker=(K.pCoreIn 2).subgroupOf C := by
    rw [MonoidHom.ker_comp_of_injective _ _ (S w).subtype_injective,hfk,
      Solvable.centralCore_eq_twoCore_of_ordinary eK]
    ext x
    change (⟨x.val,x.property.1⟩ : K) ∈ pCore 2 K ↔
      K.subtype (⟨x.val,x.property.1⟩ : K) ∈ (pCore 2 K).map K.subtype
    exact (mem_map_iff_mem K.subtype_injective).symm
  have hq2 : IsPGroup 2 q.ker := by rw [hqk]; exact (isPGroup_pCoreIn 2 K).comap_subtype
  have hCU : C ≤ normalizer (U : Set G) := inf_le_left.trans D.normalizes
  let da : Additive U ≃+ W := m.coordinate.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let d : Additive U ≃ₗ[ZMod 2] W := { da with map_smul' := ZMod.map_smul da }
  let E₀ : Representation.Equiv (elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hCU))) (rho.comp q) := {
    toLinearEquiv := d
    isIntertwining' := by intro c; apply LinearMap.ext; intro u; exact he c u.toMul }
  let e := E₀.symm
  let space := modelSpace U C hCU q rho e
  let F := U ⊓ centralizer (K : Set G)
  have hF : space F ≤ constantLine := by
    intro u hu
    change (e u).toMul.val ∈ F at hu
    have hfix := (m.fixed_iff (e u).toMul).mp hu.2
    have hcoord : (m.coordinate (e u).toMul).toAdd=u := E₀.apply_symm_apply u
    apply (mem_constantLine u).mpr
    rcases hfix with hfix | hfix
    · left
      have hh := congrArg (fun x : U => (m.coordinate x).toAdd) hfix
      simpa only [hcoord,map_one,toAdd_one] using hh
    · right
      have hh := congrArg (fun x : U => (m.coordinate x).toAdd) hfix
      exact hcoord.symm.trans (hh.trans m.constant_coordinate)
  have hnf : ¬ ∀ a : A, rho a w=w := by
    intro hh
    exact hv ((m.mem_fixed_iff v).mpr ((core_fixed_iff_constant (by simp) w).mp hh))
  have hJC : J ≤ C := Solvable.firstCentralizerResidual_le K v.val
  have hQC : Q ≤ C := (pCoreIn_le 2 J).trans hJC
  have hEC : E ≤ C := hE.trans hQC
  have hJN : J ≤ normalizer (U : Set G) := hJC.trans hCU
  have hPU : ⁅U,J⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hJN
  have hUC : U ≤ C := le_inf D.le_component (by
    intro u hu
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) v)))
  have hCN : C ≤ normalizer (J : Set G) := by
    change C ≤ normalizer (Solvable.firstCentralizerResidual K v.val : Set G)
    rw [Solvable.firstCentralizerResidual_eq]
    exact C.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))
  have hPQ : ⁅U,J⁆ ≤ Q := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 U).to_le hPU)
    (le_normalizer_iff_commutator_le_right.mp (hUC.trans hCN))
    (normalizer_commutator_ge_right U J)
  have hJR : (J.subgroupOf C).map q=residual w := by
    change (J.comap C.subtype).map ((S w).subtype.comp f)=_
    rw [show J=(primeToResidual 3 C).map C.subtype from Solvable.firstCentralizerResidual_eq K v.val,
      comap_map_eq_self_of_injective C.subtype_injective,←map_map,
      map_primeToResidual_of_surjective 3 f hf]
    rfl
  have hQR : (Q.subgroupOf C).map q=(residual w).pCoreIn 2 := by
    rw [←pCoreIn_subgroupOf 2 J C hJC,map_pCoreIn_of_ker_isPGroup q hq2,hJR]
  have htop : space U=⊤ := by apply top_unique; intro u _; exact (e u).toMul.property
  have hspace : space ⁅U,J⁆=moved w := by
    have hh := modelSpace_commutator U C hCU q rho e U J le_rfl hJN
      (fun a ha => ⟨⟨a,hJC ha⟩,ha,fun _ => rfl⟩)
    change space ⁅U,J⁆=subspaceCommutator rho (space U) ((J.subgroupOf C).map q) at hh
    rwa [htop,hJR] at hh
  have hcomm : subspaceCommutator rho (moved w) ((E.subgroupOf C).map q) ≤ constantLine := by
    have hh := modelSpace_commutator U C hCU q rho e ⁅U,J⁆ E hPU (hEC.trans hCU)
      (fun a ha => ⟨⟨a,hEC ha⟩,ha,fun _ => rfl⟩)
    change space ⁅⁅U,J⁆,E⁆=subspaceCommutator rho (space ⁅U,J⁆) ((E.subgroupOf C).map q) at hh
    rw [hspace] at hh
    rw [←hh]
    intro u hu
    apply hF
    apply hc
    rw [commutator_comm]
    exact commutator_mono hPQ le_rfl hu
  have hEq : E ≤ K.pCoreIn 2 := by
    intro x hx
    have hax : q ⟨x,hEC hx⟩ ∈ (residual w).pCoreIn 2 :=
      hQR.le (mem_map_of_mem q (hE hx))
    have hz := radical_faithful_mod_constants w hnf _ hax (by
      intro u hu
      exact hcomm (Submodule.subset_span ⟨q ⟨x,hEC hx⟩,mem_map_of_mem q hx,u,hu,rfl⟩))
    have hh : (⟨x,hEC hx⟩ : C) ∈ q.ker := hz
    rwa [hqk] at hh
  have hEU : space (E ⊓ U) ≤ fixedModuloLine ((residual w).pCoreIn 2) := by
    have hh := modelSpace_commutator U C hCU q rho e (E ⊓ U) Q inf_le_right
      (hQC.trans hCU) (fun a ha => ⟨⟨a,hQC ha⟩,ha,fun _ => rfl⟩)
    change space ⁅E ⊓ U,Q⁆=subspaceCommutator rho (space (E ⊓ U)) ((Q.subgroupOf C).map q) at hh
    rw [hQR] at hh
    intro u hu
    apply (mem_fixedModuloLine _ _).mpr
    intro a ha
    apply hF
    apply hc
    apply commutator_mono inf_le_left le_rfl
    change rho a u-u ∈ space ⁅E ⊓ U,Q⁆
    rw [hh]
    exact Submodule.subset_span ⟨a,ha,u,hu,rfl⟩
  have hcardEU : Nat.card (E ⊓ U : Subgroup G) ≤ 4 := by
    let j : (E ⊓ U : Subgroup G) → fixedModuloLine ((residual w).pCoreIn 2) :=
      fun x => ⟨e.symm (Additive.ofMul ⟨x.val,x.property.2⟩),hEU (by
        change (e (e.symm _)).toMul.val ∈ E ⊓ U
        rw [e.apply_symm_apply]
        exact x.property)⟩
    apply (Nat.card_le_card_of_injective j ?_).trans (radical_fixed_mod_constants_card w hnf)
    intro x y hxy
    have hh := e.symm.injective (congrArg Subtype.val hxy)
    exact Subtype.ext (congrArg (fun u : Additive U => u.toMul.val) hh)
  let Ei := E.subgroupOf K
  let pi := QuotientGroup.mk' (ChapterC.blockU K)
  have hcardIm : Nat.card (Ei.map pi) ≤ 2 :=
    (Nat.card_le_card_of_injective (inclusion (map_mono (show Ei ≤ pCore 2 K from
      fun x hx => (mem_map_iff_mem K.subtype_injective).mp (hEq hx))))
      (inclusion_injective _)).trans (ChapterC.alternatingSix_core_image_card_le_two eK)
  have hker : (Ei ⊓ pi.ker).map K.subtype=E ⊓ U := by
    rw [QuotientGroup.ker_mk',map_inf _ _ _ K.subtype_injective,
      map_subgroupOf_eq_of_le (hEq.trans (pCoreIn_le 2 K)),hU]
  have hcKer : Nat.card (Ei ⊓ pi.ker : Subgroup K) ≤ 4 := by
    rw [←card_map_of_injective K.subtype_injective,hker]
    exact hcardEU
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map Ei pi
  rw [Nat.card_congr (subgroupOfEquivOfLe (hEq.trans (pCoreIn_le 2 K))).toEquiv] at hprod
  rw [←hprod]
  exact (Nat.mul_le_mul hcKer hcardIm)


/-- The center bound uses the literal quotient of the point residual
radical by the augmentation fixed line, including a possible central cover. -/
theorem core_point_radical_quotient_center_card [Group.IsPerfect K]
    (D : ChosenModule T K U) (m : CoreMarking D)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hU : (ChapterC.blockU K).map K.subtype=U)
    (v : U) (hv : v.val ∉ centralizer (K : Set G))
    (z : G) (hfix : U ⊓ centralizer (K : Set G)=zpowers z)
    (hzQ : zpowers z ≤ (Solvable.firstCentralizerResidual K v.val).pCoreIn 2) :
    let Q := (Solvable.firstCentralizerResidual K v.val).pCoreIn 2
    ∀ hn : ((zpowers z).subgroupOf Q).Normal,
      letI := hn
      Nat.card (center (Q ⧸ (zpowers z).subgroupOf Q)) ≤ 4 := by
  let Q := (Solvable.firstCentralizerResidual K v.val).pCoreIn 2
  let N := (zpowers z).subgroupOf Q
  dsimp only
  intro hn
  let : N.Normal := hn
  let pi := QuotientGroup.mk' N
  let Ei := (center (Q ⧸ N)).comap pi
  let E := Ei.map Q.subtype
  have hEQ : E ≤ Q := map_subtype_le Ei
  have hc : ⁅E,Q⁆ ≤ U ⊓ centralizer (K : Set G) := by
    rw [hfix]
    apply commutator_le.mpr
    rintro a ⟨a,ha,rfl⟩ b hb
    have hh : pi ⁅a,(⟨b,hb⟩ : Q)⁆=1 := by
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.mp ha _).symm
    exact (QuotientGroup.eq_one_iff (N := N) ⁅a,(⟨b,hb⟩ : Q)⁆).mp hh
  have hbound : Nat.card E ≤ 8 :=
    core_point_radical_central_mod_fixed_card D m eK hU v hv E hEQ hc
  have hNE : N ≤ Ei := fun n hn => by
    change pi n ∈ center (Q ⧸ N)
    have he : pi n=1 := (QuotientGroup.eq_one_iff (N := N) n).mpr hn
    rw [he]
    exact one_mem _
  have hprod := IsElementaryAbelian.card_inf_ker_mul_card_map Ei pi
  have him : Ei.map pi=center (Q ⧸ N) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  rw [QuotientGroup.ker_mk',inf_eq_right.mpr hNE,him] at hprod
  have hN : Nat.card N=2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hzQ).toEquiv,←hfix]
    exact m.card_fixed
  have hEcard : Nat.card Ei=Nat.card E := (card_map_of_injective Q.subtype_injective).symm
  rw [hN,hEcard] at hprod
  change Nat.card (center (Q ⧸ N)) ≤ 4
  omega


open Chapter14.Section03.FaithfulSource Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V A B : Subgroup G}

theorem original_linear_pair_mixed_commute_of_selected_six
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
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
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
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
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ = ⊥ := by
  dsimp only
  intro g h₁ h₂
  by_contra hm
  obtain ⟨hfixed,_,_,hU,_,hEQ,_,hc,hn,hlo⟩ := original_linear_pair_mixed_six_center_bounds
    h₀ h structural modules D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
    h1332 fixed hlin eL hM hZV W hW hTW hB hfusion z hzT hzL hAz hK hHN hKM hfK eK
    g h₁ h₂ hm
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let J := Solvable.firstCentralizerResidual L z.val
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨DK,⟨mK⟩,hfix,_,_,_,_⟩ := component_core_marking_of_source_fixed
    h₀ h structural m h1332 fixed hindexL z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K = U := by
    have hh := component_seed_split h₀ hzT hz1 hK.1 (h1332 K hfK).1
    rw [component_full_fixed_line h structural z.val hz1 hzT hindexL K hK.1 hKM,
      sup_eq_left.mpr (show zpowers z.val ≤ U from hfix.symm ▸ inf_le_left)] at hh
    exact hh
  have hdU : m.constant.val ∈ U := hsplit ▸
    le_conjugateSpanBy _ _ (m.constant_mem_central_four h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hrec := component_reciprocal_residual_of_ordinary_six h₀ h structural m hzT hz1
    hK hHN (component_quotient_quasisimple h1332 hfK) eK eL
  have hzQ : zpowers z.val ≤ J.pCoreIn 2 := by
    rw [←hc]
    exact (Subgroup.commutator_le_sup _ _).trans (sup_le hEQ le_rfl)
  let : Group.IsPerfect (K.subgroupOf (K ⊔ (T : Subgroup G))) := hfK.1.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ K ⊔ (T : Subgroup G) from le_sup_left)).surjective
  have hupper := core_point_radical_quotient_center_card DK mK eK hU
    ⟨m.constant.val,hdU⟩ hdK z.val hfix (by simpa only [hrec] using hzQ)
  dsimp only at hupper
  rw [hrec] at hupper
  have hhi := hupper hn
  omega
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

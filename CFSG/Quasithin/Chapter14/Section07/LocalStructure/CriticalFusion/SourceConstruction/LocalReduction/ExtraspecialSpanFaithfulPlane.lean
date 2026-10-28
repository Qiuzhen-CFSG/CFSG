module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialSpanModule
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Flags

/-!
# The original commutator span inside a faithful chief interval

In the faithful case of 14.7.20(2), the selected critical involution has a
square root in the literal Q. The commuting point cubic is fixed-free on
the six-dimensional chief action. Even kernel dimensions identify the root's
fixed plane with the involution's displacement. Since [R,Q] = V and
[Uα,B] ≤ [S,Q] = R, that plane is exactly the image of R in B/N and the
full Q-fixed space. Its point-residual action is irreducible and noncentral.

The final application constructs the original chief coordinates, proves
N's relative index in R ∩ B is four, and retains the exact action kernel
O₂(H) and both central flanks. The count on all of R/V and its Core
recognition are separate subsequent steps; neither is assumed here.
Source: Aschbacher–Smith 14.7.23(2), printed pp.1050–1051,
refs/quasithin.pdf. The stated earlier source implications retain their
existing producers and final discharge with qt-d-14775-source.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

theorem extraspecial_faithful_chief_span_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) =
      s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L) ∧
    Module.finrank (ZMod 2) (s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L)) = 2 ∧
    ∀ w ∈ s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L),
      (∀ a : F.Li L 1, ρ (inclusion ((F.Li_le L 1).trans inf_le_right) a) w = w) → w = 0 := by
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  obtain ⟨σ,hσ,hf,hd,hi⟩ := extraspecial_point_noncentral_chief
    h hab structural previous hex hcard hexp hB hUN s hm
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff (starMap F)
    (QuotientGroup.mk'_surjective _) σ).mp (hσ ▸ inferInstance)
  let : ((F.Li L 1).subgroupOf F.H).Normal := hn
  let Z := star F (F.Li L 1)
  let : Z.Normal := hn.map (starMap F) (QuotientGroup.mk'_surjective _)
  have hZc : Nat.card Z = 3 := pointResidual_star_card_of_normal h structural hn
  have hZ : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hZc)
  have hfixed : invariants (σ.comp Z.subtype) = ⊥ := by
    by_contra hh
    have hk := le_ker_of_normal_invariants_ne_bot σ Z hh
    have hb : Z = ⊥ := by
      apply bot_unique
      intro z hz
      exact hf ((hk hz).trans (map_one σ).symm)
    have hz1 : Nat.card Z = 1 := by rw [hb]; exact Nat.card_unique
    omega
  have hfree (w : W) (hw : ∀ a : F.Li L 1,
      ρ (inclusion ((F.Li_le L 1).trans inf_le_right) a) w = w) : w = 0 := by
    have hh : w ∈ invariants (σ.comp Z.subtype) := by
      rintro ⟨z,hz⟩
      obtain ⟨a,ha,rfl⟩ := hz
      change σ (starMap F a) w = w
      rw [show σ (starMap F a) = ρ a from congrArg (fun ψ => ψ a) hσ]
      exact hw ⟨a,ha⟩
    simpa only [hfixed,Submodule.mem_bot] using hh
  obtain ⟨a,b,ha,hane,ha2,_,_,hb,hba,hbo⟩ :=
    exists_extraspecial_critical_actor_square_root h hab structural previous faithful ⟨e⟩ c hs
  let P := pResidual 2 (HStar F.H)
  let : IsExtraspecial 3 P := hex.of_mulEquiv (residualStarEquiv F)
  have hP : Nat.card P = 27 := (Nat.card_congr (residualStarEquiv F).toEquiv).symm.trans hcard
  have hExp : Monoid.exponent P = 3 :=
    (Monoid.exponent_eq_of_mulEquiv (residualStarEquiv F)).symm.trans hexp
  have hlo : 2 ≤ Module.finrank (ZMod 2) (ρ a-1).range := by
    by_contra hh
    have hsmall : fixedCodim σ (zpowers (starMap F a)) ≤ 1 := by
      rw [fixedCodim_zpowers_eq_displacement_rank]
      change Module.finrank (ZMod 2) (σ.comp (starMap F) a-1).range ≤ 1
      rw [hσ]
      omega
    exact hane (ExtraspecialBinarySix.rank_one_actor_trivial σ hf P hP hExp
      (Theory.GroupTheory.centralizer_pResidual_le_of_pCore_eq_bot (pCore_quotient_pCore_eq_bot 2))
      (starMap F a) ha2 hsmall)
  have hr : Module.finrank (ZMod 2) (ρ a-1).range = 2 := le_antisymm
    (extraspecial_centralizer_section_displacement h hab structural previous hex hcard hexp c hs hB hUN s a ha) hlo
  have hbR : starMap F b ∈ star F (F.Ri L 1) := by
    rw [←(core_product_of_point_normal h hab structural hn).2]
    exact mem_map_of_mem (starMap F) hb
  have hcomm : ∀ z : Z, Commute (σ z) (σ (starMap F b)) := by
    intro z
    exact (show Commute (z : HStar F.H) (starMap F b) from
      point_core_star_centralizes_of_normal h structural hn hbR z z.property).map σ
  have hsq : (σ (starMap F b))^2=σ (starMap F a) := by rw [←map_pow,hba]
  have h4 : (σ (starMap F b))^4=1 := by
    rw [←map_pow,show (starMap F b)^4=1 from hbo ▸ pow_orderOf_eq_one _,map_one]
  obtain ⟨heq,hk⟩ := order_four_fixed_plane_of_commuting_three_group σ Z hZ hfixed hd _ h4
    (by rw [hsq,show σ (starMap F a)=ρ a from congrArg (fun ψ => ψ a) hσ]; exact hr) hcomm
  rw [hsq,show σ (starMap F a)=ρ a from congrArg (fun ψ => ψ a) hσ,
    show σ (starMap F b)=ρ b from congrArg (fun ψ => ψ b) hσ] at heq
  rw [show σ (starMap F b)=ρ b from congrArg (fun ψ => ψ b) hσ] at hk
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  have hRQ : ⁅Q T L,R⁆ ≤ N := by
    rw [commutator_comm,extraspecial_commutator_span_core_eq_seed h hab structural previous faithful ⟨e⟩ c hs]
    exact (le_conjugateSpanBy V F.H).trans hUN
  have hfixR : s.imageSpace R ≤ invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) := by
    intro w hw q
    exact s.fixed_on_imageSpace_of_commutator_le (Q T L) R hRQ q q.property w hw
  have hfixb : invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) ≤ (ρ b-1).ker := by
    intro w hw
    exact sub_eq_zero.mpr (hw ⟨b,hb⟩)
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  have hCT : centralizer (F.U : Set G) ≤ (T : Subgroup G) :=
    (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU).trans
      ((pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))).trans_eq
        (map_subgroupOf_eq_of_le (F.invariant 1)))
  have hBQ : B ≤ Q T L := by
    change B ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2
    rw [←h.centralizer_LT structural]
    exact le_inf ((hB.trans hCT).trans le_sup_right)
      (hB.trans (centralizer_le (le_conjugateSpanBy V F.H)))
  obtain ⟨_,_,g,hg,hgU,_⟩ := extraspecial_critical_interchange h hab structural previous faithful ⟨e⟩ c hs
  have hAS : c.Uα ≤ conjugateSpanBy F.U L := by
    rw [←hgU,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup_of_le (⟨g,hg⟩ : L) le_rfl
  have hmove : ⁅c.Uα,B⁆ ≤ R := by
    exact (commutator_mono hAS hBQ).trans_eq (original_span_core_commutator h hab structural)
  have hrR : (ρ a-1).range ≤ s.imageSpace R :=
    s.displacement_range_le_imageSpace_of_commutator_le c.Uα R hmove a ha
  have hR : s.imageSpace R = (ρ b-1).ker :=
    le_antisymm (hfixR.trans hfixb) (heq.symm ▸ hrR)
  exact ⟨le_antisymm (hfixb.trans hR.symm.le) hfixR,by rw [hR]; exact hk,fun w _ => hfree w⟩


private theorem spanFaithful_irreducible_plane
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (τ : Representation (ZMod 2) A X) (hd : Module.finrank (ZMod 2) X = 2)
    (hf : ∀ x, (∀ a, τ a x = x) → x = 0) : τ.IsIrreducible := by
  let : Nontrivial X := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank (ZMod 2) X)
  rw [Representation.IsIrreducible,isSimpleOrder_iff]
  refine ⟨inferInstance,fun N => ?_⟩
  by_cases hb : N = ⊥
  · exact Or.inl hb
  by_cases ht : N = ⊤
  · exact Or.inr ht
  exfalso
  have hNb : N.toSubmodule ≠ ⊥ := fun hh => hb (Subrepresentation.toSubmodule_injective hh)
  have hNt : N.toSubmodule ≠ ⊤ := fun hh => ht (Subrepresentation.toSubmodule_injective hh)
  have hpos : 0 < Module.finrank (ZMod 2) N.toSubmodule :=
    Nat.pos_of_ne_zero (fun hh => hNb (Submodule.finrank_eq_zero.mp hh))
  have hlt := Submodule.finrank_lt hNt
  have hdim : Module.finrank (ZMod 2) N.toSubmodule = 1 := by omega
  apply hNb
  apply bot_unique
  intro x hx
  exact hf x (fun a => by
    have hh := BinaryParabolicNatural.linear_one_trivial hdim
      (LinearMap.GeneralLinearGroup.toLinearEquiv (N.toRepresentation.asGroupHom a))
    exact congrArg (fun f : N.toSubmodule ≃ₗ[ZMod 2] N.toSubmodule => (f ⟨x,hx⟩ : X)) hh)

open BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The faithful chief interval meets the original commutator span in one
noncentral irreducible plane for the literal point residual. -/
theorem extraspecial_faithful_chief_span_irreducible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    {B N : Subgroup G} (hB : B ≤ centralizer (F.U : Set G)) (hUN : F.U ≤ N)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) F.H W} [ρ.IsIrreducible]
    (s : BinaryConjugationSection F.H B N ρ)
    (hm : ¬ ⁅F.Li L 1,B⁆ ≤ N)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection) :
    ∃ D : Subrepresentation (ρ.comp (inclusion ((F.Li_le L 1).trans inf_le_right))),
      D.toSubmodule = s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L) ∧
      Module.finrank (ZMod 2) D.toSubmodule = 2 ∧
      IsIrreducible D.toRepresentation ∧ ¬ Central ⊥ D ∧
      invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) = D.toSubmodule := by
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  let j : F.Li L 1 →* F.H := inclusion ((F.Li_le L 1).trans inf_le_right)
  let D : Subrepresentation (ρ.comp j) := {
    toSubmodule := s.imageSpace R
    apply_mem_toSubmodule a w hw := s.imageSpace_apply_mem R (j a)
      ((original_commutator_span_normalized h structural).1
        ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)) (F.Li_le L 1 a.property).1)) w hw }
  let : Finite W := Finite.of_surjective (fun b : B => (s.coordinates b).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨hfixed,hd,hfree⟩ :=
    extraspecial_faithful_chief_span_plane h hab structural previous faithful he hB hUN s hm c hs
  have hirr : IsIrreducible D.toRepresentation := spanFaithful_irreducible_plane _ hd (by
    intro w hw
    apply Subtype.ext
    exact hfree w w.property (fun a => congrArg Subtype.val (hw a)))
  refine ⟨D,rfl,hd,hirr,?_,hfixed⟩
  intro hc
  have hz : D = ⊥ := by
    apply bot_unique
    intro w hw
    exact hfree w hw (fun a => sub_eq_zero.mp (hc a w hw))
  have hh : Module.finrank (ZMod 2) D.toSubmodule = 0 := by
    rw [hz]
    exact finrank_bot _ _
  change Module.finrank (ZMod 2) D.toSubmodule = 2 at hd
  omega


open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- The original order-64 interval has an actual irreducible noncentral
intersection with R, of relative index four and equal to its full Q-fixed space. -/
theorem extraspecial_span_faithful_interval
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hm : ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype) :
    ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (ρ : Representation (ZMod 2) F.H W)
      (s : BinaryConjugationSection F.H (B.val.map F.H.subtype) (N.val.map F.H.subtype) ρ)
      (D : Subrepresentation (ρ.comp (inclusion ((F.Li_le L 1).trans inf_le_right)))),
      D.toSubmodule = s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L) ∧
      Module.finrank (ZMod 2) D.toSubmodule = 2 ∧
      IsIrreducible D.toRepresentation ∧ ¬ Central ⊥ D ∧
      invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) = D.toSubmodule ∧
      (N.val.map F.H.subtype).relIndex
        (conjugateSpanBy ⁅F.U,Q T L⁆ L ⊓ B.val.map F.H.subtype) = 4 := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨τ,⟨sU⟩⟩ := exists_section F
  let C := (centralizer (F.U : Set G)).subgroupOf F.H
  have hC : IsPGroup 2 C :=
    ((isPGroup_pCoreIn 2 F.H).to_le
      (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU)).comap_subtype
  have hBC' : B.val ≤ C := fun b hb => hBC (mem_map_of_mem F.H.subtype hb)
  let : IsElementaryAbelian 2 (Section N B) := chief_elementary N B hNB (hC.to_le hBC')
  let ρ := binarySectionRepresentation N B
  let : ρ.IsIrreducible := binarySection_irreducible N B hNB
  let s := ambientBinarySection F.H N B hNB.le
  obtain ⟨c,hs,_⟩ := extraspecial_span_source_reduction h hab structural previous faithful he
  obtain ⟨D,hD,hd,hirr,hcentral,hfixed⟩ :=
    extraspecial_faithful_chief_span_irreducible h hab structural previous faithful he hBC hUN s hm c hs
  refine ⟨Additive (Section N B),inferInstance,inferInstance,ρ,s,D,hD,hd,hirr,hcentral,hfixed,?_⟩
  let R := conjugateSpanBy ⁅F.U,Q T L⁆ L
  have him : s.imageSpace (R ⊓ B.val.map F.H.subtype) = s.imageSpace R := by
    apply le_antisymm (s.imageSpace_mono inf_le_left)
    intro w hw
    obtain ⟨b,hb,rfl⟩ := (s.mem_imageSpace_iff R w).mp hw
    exact (s.mem_imageSpace_iff _ _).mpr ⟨b,⟨hb,b.property⟩,rfl⟩
  have hc := s.imageSpace_card_eq_relIndex (R ⊓ B.val.map F.H.subtype) inf_le_right
  rw [him,←hD,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd] at hc
  exact hc.symm

open NoncentralChiefRefinement BinaryLinearThree.ParabolicCyclic.ChiefCounts in
/-- Original-source application of the faithful plane calculation. The
central case remains available; the faithful case retains the exact chief
action kernel and both central flanks, and constructs the intersected plane. -/
theorem extraspecial_span_central_or_faithful_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U ∧
          ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
            (ρ : Representation (ZMod 2) F.H W)
            (s : BinaryConjugationSection F.H (B.val.map F.H.subtype) (N.val.map F.H.subtype) ρ)
            (D : Subrepresentation (ρ.comp (inclusion ((F.Li_le L 1).trans inf_le_right)))),
            D.toSubmodule = s.imageSpace (conjugateSpanBy ⁅F.U,Q T L⁆ L) ∧
            Module.finrank (ZMod 2) D.toSubmodule = 2 ∧
            IsIrreducible D.toRepresentation ∧ ¬ Central ⊥ D ∧
            invariants (ρ.comp ((Q T L).subgroupOf F.H).subtype) = D.toSubmodule ∧
            (N.val.map F.H.subtype).relIndex
              (conjugateSpanBy ⁅F.U,Q T L⁆ L ⊓ B.val.map F.H.subtype) = 4) := by
  obtain ⟨hp,hc | ⟨N,B,hNB,hUN,hBC,hm,hsize,hker,hupper,hlower⟩⟩ :=
    extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he
  · exact ⟨hp,Or.inl hc⟩
  · exact ⟨hp,Or.inr ⟨N,B,hNB,hUN,hBC,hm,hsize,hker,hupper,hlower,
      extraspecial_span_faithful_interval h hab structural previous faithful he N B hNB hUN hBC hm⟩⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction

module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.F92Kernel
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.QuadraticBound
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Actors
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.OffenderTransport

/-!
# The original F.9.16 witness in Section 15.3

The genuine F.9.1 setup and the abelian full V-span produce an odd critical
pair. The two strict denominators select a quadratic actor by reversal and
the common-center rank estimate. A full left denominator gives the same
bound directly from its displacement line. With a full right denominator,
15.3.47 excludes commuting small spans: each conjugate seed centralizes
the displacement of its own element, so the normalizer test would force
the critical action to be trivial. The inverse terminal-edge conjugator
then returns a common-center actor to the original local group.

In all branches the actual actor is placed inside O₂((YT)∩H). Its image in
H/O₂(H) is nontrivial elementary abelian, quadratic on the literal U_H/Z,
and has fixed codimension at most twice its rank. Thus the source action
has q≤2. The hypotheses are the original earlier 15.3.47,48,50,62 inputs;
no F.9.16 callback or reductio-only 15.3.49 omega-center hypothesis is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.16(1–4),
printed pp.323–324, and 15.3.64, printed p.1151.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound

/-- Recover the literal Section 15.3 source record from the proved F.9.1
hypothesis, including its derived containment in the Sylow subgroup. -/
theorem SourceF91.ofF91 {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {Y V ZS Z H : Subgroup G} [IsElementaryAbelian 2 V]
    (h : (f91Setup T Y V ZS Z H).Hypothesis) : SourceF91 T Y V ZS Z H where
  residual := h.residual
  normalizes_Y := h.normalizes_L
  characteristic_Y := h.characteristic_L
  v_le_sylow := h.V_le_T
  v_reduced := ⟨h.reduced.normal, h.reduced.quotient_pCore_eq_bot⟩
  sylow_centralizer := h.sylow_centralizer
  z_card := h.point_card
  normalizes_Z := h.normalizes_point
  z_lt := h.point_lt
  zs_le := h.plus_le
  a_centralizes := h.H_centralizes
  a_contains := h.local_le
  a_characteristic := h.characteristic_H
  a_kernel := h.kernel_core
  b_normalizes := h.local_normalizes
  b_irreducible := h.irreducible
  c_normalizer := h.normalizer_control
  d_core := h.generated_core
  e_commutators := h.commutator_lifting

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound.OriginalF916
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open PairConsequences.ReversedSourceData
variable {G E : Type*} [Group G] [Finite G]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

noncomputable def conjugationSection {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G)) :
    ConjugationSection H U Z a.representation where
  le := a.le_local
  normalizes := a.normalizes
  centralizes := hz
  line_le := a.kernel_le
  quotient := (MulEquiv.multiplicativeAdditive (U ⧸ Z.subgroupOf U)).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Z.subgroupOf U))
  surjective := (MulEquiv.multiplicativeAdditive _).symm.surjective.comp
    (QuotientGroup.mk'_surjective _)
  kernel := by ext u; exact QuotientGroup.eq_one_iff u
  conjugates := a.conjugation

theorem quadratic_member_of_common_line {H U Z A C : Subgroup G}
    [IsElementaryAbelian 2 A]
    {ρ : Representation (ZMod 2) (Source.Hstar H) E}
    (s : ConjugationSection H U Z ρ) (hA : A ≤ H)
    (hC : Nat.card C = 2) (hc : ⁅U,A⁆ ≤ C)
    (hfix : A ≤ centralizer (C : Set G)) (hne : ¬ ⁅U,A⁆ ≤ Z) :
    QuadraticMember ρ (Source.starImage H A) := by
  let B := Source.starImage H A
  let : IsElementaryAbelian 2 B := starImage_isElementaryAbelian H A hA
  have hv (v : E) : v ∈ s.image U := by
    obtain ⟨u,hu⟩ := s.surjective (Multiplicative.ofAdd v)
    exact ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
  have hd : ∀ b ∈ B, ∀ v, ρ b v-v ∈ s.image C := by
    intro b hb v
    exact s.displacement_mem U A C (by rwa [commutator_comm]) b hb v (hv v)
  have hz : ∀ b ∈ B, ∀ z ∈ s.image C, ρ b z=z := by
    rintro _ ⟨b,hb,rfl⟩ z hz
    obtain ⟨u,hu,rfl⟩ := (s.mem_image C z).mp hz
    apply sub_eq_zero.mp
    change ρ (QuotientGroup.mk' (pCore 2 H) b) (s.quotient u).toAdd -
      (s.quotient u).toAdd = 0
    rw [s.displacement]
    apply (s.quotient_eq_zero_iff _).mpr
    change ⁅(b:G),(u:G)⁆∈Z
    have hc' : ⁅(b:G),(u:G)⁆=1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((hfix hb) u hu).symm
    rw [hc']
    exact Z.one_mem
  have hB : B ≠ ⊥ := by
    intro he
    apply hne
    rw [commutator_comm]
    apply commutator_le.mpr
    intro b hb u hu
    apply (s.quotient_eq_zero_iff ⟨⁅b,u⁆,s.commutator_mem ⟨b,hA hb⟩ ⟨u,hu⟩⟩).mp
    rw [←s.displacement ⟨b,hA hb⟩ ⟨u,hu⟩]
    have hh : QuotientGroup.mk' (pCore 2 H) ⟨b,hA hb⟩=1 := by
      have hh' : QuotientGroup.mk' (pCore 2 H) ⟨b,hA hb⟩∈B := mem_map_of_mem _ hb
      rw [he,Subgroup.mem_bot] at hh'
      exact hh'
    rw [hh,map_one,Module.End.one_apply,sub_self]
  have hdim : Module.finrank (ZMod 2) (s.image C)≤1 := by
    simpa only [hC,show Nat.log 2 2=1 from by decide] using s.image_finrank_le C
  have hbound := CommonCenter.fixedCodim_top_le_of_center_dim_le_one
    (ρ.comp B.subtype) (s.image C) hdim
    (fun b v=>hd b b.property v) (fun b z hz'=>hz b b.property z hz')
  have heq : fixedCodim (ρ.comp B.subtype) ⊤=fixedCodim ρ B := by
    change Module.finrank (ZMod 2) (E ⧸ fixedSpace (ρ.comp B.subtype) ⊤)=_
    rw [fixedSpace_comp_map,←MonoidHom.range_eq_map,B.range_subtype]
    rfl
  rw [heq] at hbound
  exact ⟨⟨hB,inferInstance⟩,fun a ha b hb v=>hz a ha _ (hd b hb v),by
    change fixedCodim ρ B≤2*Nat.log 2 (Nat.card B)
    omega⟩

omit [Finite G] in
theorem small_spans_not_commute {V ZS H Z : Subgroup G} (g : G)
    [IsMulCommutative (conjugateSpanBy V H)]
    (hZS : ZS ≤ V)
    (hcomm : ⁅conjugateSpanBy V H,(conjugateSpanBy V H).map (MulAut.conj g).toMonoidHom⁆ ≤
      (conjugateSpanBy V H).map (MulAut.conj g).toMonoidHom)
    (h47 : ∀ x ∈ centralizer (ZS : Set G), ⁅V,zpowers x⁆=⊥ ∨ NormalizingConjugatesCentralize V x)
    (hbad : ¬ ⁅(conjugateSpanBy ZS H).map (MulAut.conj g).toMonoidHom,V⁆ ≤ Z) :
    ⁅conjugateSpanBy ZS H,(conjugateSpanBy ZS H).map (MulAut.conj g).toMonoidHom⁆≠⊥ := by
  intro hc
  have hsmall := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  apply hbad
  apply le_trans _ bot_le
  rw [le_bot_iff,commutator_eq_bot_iff_le_centralizer]
  rw [conjugateSpanBy_eq_iSup_conj,Subgroup.map_iSup]
  refine iSup_le fun a=>?_
  let k := g*(a:G)
  have he (W : Subgroup G) : (W.map (MulAut.conj (a:G)).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = W.map (MulAut.conj k).toMonoidHom := by
    rw [map_map]
    congr 1
    ext x
    simp [k,MulAut.conj_apply,mul_assoc]
  rw [he]
  have hbig : V.map (MulAut.conj k).toMonoidHom ≤
      (conjugateSpanBy V H).map (MulAut.conj g).toMonoidHom := by
    rw [←he]
    exact map_mono (by
      rw [conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun a:H=>V.map (MulAut.conj (a:G)).toMonoidHom) a)
  have hsm : ZS.map (MulAut.conj k).toMonoidHom ≤
      (conjugateSpanBy ZS H).map (MulAut.conj g).toMonoidHom := by
    rw [←he]
    exact map_mono (by
      rw [conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun a:H=>ZS.map (MulAut.conj (a:G)).toMonoidHom) a)
  intro x hx
  have hxZS : x∈centralizer (ZS:Set G) :=
    (hsmall.trans (Subgroup.centralizer_le (le_conjugateSpanBy ZS H))) (hsm hx)
  rcases h47 x hxZS with hzero | htest
  · exact commutator_eq_bot_iff_le_centralizer.mp (commutator_comm V (zpowers x) ▸ hzero)
      (mem_zpowers x)
  · have hcx : ⁅V,zpowers x⁆ ≤ (conjugateSpanBy V H).map (MulAut.conj g).toMonoidHom :=
      (commutator_mono (le_conjugateSpanBy V H)
        (zpowers_le.mpr (hbig (map_mono hZS hx)))).trans hcomm
    let : IsMulCommutative ((conjugateSpanBy V H).map (MulAut.conj g).toMonoidHom) :=
      Subgroup.map_isMulCommutative (H := conjugateSpanBy V H)
        (f := (MulAut.conj g).toMonoidHom)
    have hn : V.map (MulAut.conj k).toMonoidHom ≤ normalizer ((⁅V,zpowers x⁆:Subgroup G):Set G) :=
      (hbig.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (Subgroup.centralizer_le hcx))).trans (Subgroup.centralizer_le_normalizer _)
    exact htest k hn (map_mono hZS hx)

omit [Finite G] in
private theorem member_conjugate {H A : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) E} (hAH : A≤H)
    (hA : QuadraticMember ρ (Source.starImage H A)) (g : H) :
    QuadraticMember ρ (Source.starImage H (A.map (MulAut.conj (g:G)).toMonoidHom)) := by
  have he := FusionCore.ExtraspecialElimination.ComponentReduction.starImage_map_conj H A hAH g
  change Source.starImage H (A.map (MulAut.conj (g:G)).toMonoidHom)=
    (Source.starImage H A).map (MulAut.conj (QuotientGroup.mk' (pCore 2 H) g)).toMonoidHom at he
  rw [he]
  let t := QuotientGroup.mk' (pCore 2 H) g
  have hinv (x:E) : ρ t⁻¹ (ρ t x)=x := by
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hginv (x:E) : ρ t (ρ t⁻¹ x)=x := by
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  refine ⟨hA.1.map_conj _,?_,?_⟩
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    change ρ (t*a*t⁻¹) (ρ (t*b*t⁻¹) v-v)=ρ (t*b*t⁻¹) v-v
    simp only [map_mul,Module.End.mul_apply,map_sub,hinv]
    have hh:=congrArg (fun x=>ρ t x) (hA.2.1 a ha b hb (ρ t⁻¹ v))
    simpa only [map_sub,hginv] using hh
  · rw [fixedCodim_map_conj,rank_map_conj]
    exact hA.2.2

omit [Finite G] in
private theorem placed_at_neighbor {L T H A : Subgroup G}
    {ρ : Representation (ZMod 2) (Source.Hstar H) E}
    (w : Vertex L T H) (hw : (graph L T H).Adj (base L T H true) w)
    (hc : A≤(edgeGroup L T H (base L T H true) w).pCoreIn 2)
    (hA : QuadraticMember ρ (Source.starImage H A)) :
    ∃ B : Subgroup G, B≤((L⊔T)⊓H).pCoreIn 2 ∧
      QuadraticMember ρ (Source.starImage H B) := by
  obtain ⟨g,hg⟩ := exists_neighbor_transporter hw
  have ht : inG0 (L:=L) (T:=T) g⁻¹ • w=base L T H false := by
    rw [←hg]
    exact inv_smul_smul (inG0 g) _
  have he : (edgeGroup L T H (base L T H true) w).map
      (MulAut.conj ((g⁻¹:H):G)).toMonoidHom=(L⊔T)⊓H := by
    change (edgeGroup L T H (base L T H true) w).map
      (MulAut.conj (inG0 (L:=L) (T:=T) g⁻¹:G)).toMonoidHom=_
    rw [edgeGroup,map_inf _ _ _ (MulAut.conj _).injective,
      ←vertexGroup_smul L T H (inG0 g⁻¹),←vertexGroup_smul L T H (inG0 g⁻¹),
      inG0_one,ht,vertexGroup_base,vertexGroup_base]
    exact inf_comm _ _
  have hp : A.map (MulAut.conj ((g⁻¹:H):G)).toMonoidHom≤((L⊔T)⊓H).pCoreIn 2 := by
    have hh:=map_mono (f:=(MulAut.conj ((g⁻¹:H):G)).toMonoidHom) hc
    rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
      (MulAut.conj _).injective,he] at hh
    exact hh
  have hAH : A≤H := by
    have hh:=hc.trans ((pCoreIn_le 2 _).trans inf_le_left)
    rwa [vertexGroup_base] at hh
  exact ⟨_,hp,member_conjugate hAH hA g⁻¹⟩

theorem exists_placed_quadratic_member (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] [IsElementaryAbelian 2 D.VH]
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (s : ConjugationSection D.H D.UH D.V₁ ρ)
    (h62 : ∀ g:G, D.V⊓D.V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (h47 : ∀ x∈centralizer (D.Vplus:Set G),
      ⁅D.V,zpowers x⁆=⊥ ∨ NormalizingConjugatesCentralize D.V x) :
    ∃ A : Subgroup G, A≤(D.LT⊓D.H).pCoreIn 2 ∧ QuadraticMember ρ (Source.starImage D.H A) := by
  have hcore : D.V≤D.QH := (le_conjugateSpanBy D.V D.H).trans
    (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.VH)
      h.VH_le_H (le_normalizer_conjugateSpanBy D.V D.H))
  have hb := h.b_bounds_of_intersecting_conjugates_commute hcore h62
  have hdist : 3≤criticalDistance D.L (D.T:Subgroup G) D.H D.V ∧
      Odd (criticalDistance D.L (D.T:Subgroup G) D.H D.V) := by
    simpa only [f9_criticalDistance_eq D h] using hb
  obtain ⟨c,hbc,_⟩ := f9_criticalPair_bounds D h hdist
  have hlength (c' : CriticalPair D.L (D.T:Subgroup G) D.H D.V) :
      3≤c'.path.length := by rw [c'.length_eq]; exact hdist.1
  have geo (c' : CriticalPair D.L (D.T:Subgroup G) D.H D.V) :=
    f9_earlierGeometry D h c' (hlength c') h62
  have huv : D.UH≤D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hγH : c.Ugamma D.Vplus≤D.H := (map_mono huv).trans (geo c).Vgamma_H
  have hUA : D.UH≤normalizer (c.Aone D.V₁:Set G) := by
    apply le_trans (huv.trans (geo c).VH_endpoint)
    rw [c.vertexGroup_gamma,CriticalPair.Aone,←map_equiv_normalizer_eq]
    exact map_mono (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hUgA : c.Ugamma D.Vplus≤centralizer (c.Aone D.V₁:Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [CriticalPair.Ugamma,CriticalPair.Aone,←map_commutator]
    exact (congrArg (fun A:Subgroup G=>A.map (MulAut.conj (c.gb:G)).toMonoidHom)
      (commutator_eq_bot_iff_le_centralizer.mpr (h.UH_le_H.trans h.H_centralizes))).trans (map_bot _)
  have hcardA : Nat.card (c.Aone D.V₁)=2 := by
    rw [CriticalPair.Aone,card_map_of_injective (MulAut.conj _).injective,h.point_card]
  let : IsElementaryAbelian 2 (Source.UH D.H D.Vplus) := ‹IsElementaryAbelian 2 D.UH›
  let : IsElementaryAbelian 2 (Source.VH D.H D.V) := ‹IsElementaryAbelian 2 D.VH›
  let : IsMulCommutative (conjugateSpanBy D.V D.H) :=
    ‹IsElementaryAbelian 2 D.VH›.toIsMulCommutative
  let : IsElementaryAbelian 2 (c.Ugamma D.Vplus) := IsElementaryAbelian.map _
  have hbad := f9_commutator_not_le_Aone D h c hbc
  have place (c' : CriticalPair D.L (D.T:Subgroup G) D.H D.V)
      (hq : QuadraticMember ρ (Source.starImage D.H (c'.Ugamma D.Vplus))) :
      ∃ A : Subgroup G, A≤(D.LT⊓D.H).pCoreIn 2 ∧ QuadraticMember ρ (Source.starImage D.H A) := by
    have hc' := (map_mono huv).trans (f9_endpoint_edge_cores D h c' (hlength c')).2
    have hadj : (graph D.L (D.T:Subgroup G) D.H).Adj (base _ _ _ true) c'.second := by
      have hh:=c'.path.adj_getVert_succ (i:=1) (by have hh:=hlength c'; omega)
      rwa [c'.first] at hh
    exact placed_at_neighbor c'.second hadj hc' hq
  by_cases hDγ : Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁<c.Ugamma D.Vplus
  · by_cases hDH : Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁)<D.UH
    · obtain ⟨d,_,_,_,_,hq⟩ := Reorientation.exists_quadratic_selection D.Vplus D.V₁ c s
        (f9_section_faithful D h s) hbc h.plus_le (fun c'=>(geo c').Vgamma_H)
        (huv.trans (geo c).VH_endpoint) (geo c).first_kernel hDH hDγ
        (fun c'=>(c'.quadratic_star_on_Utilde D.Vplus D.V₁ s h.plus_le (geo c').VH_endpoint).2)
        (fun c' _ hc=>f9_fixedCodim_le_twice_rank D h c' (hlength c') s hc)
      exact place d hq
    · have he := eq_of_le_of_not_lt (commutatorPreimage_le D.UH
        (c.Ugamma D.Vplus) (c.Aone D.V₁)) hDH
      have hc : ⁅D.UH,c.Ugamma D.Vplus⁆≤c.Aone D.V₁ := by
        conv_lhs => lhs; rw [←he]
        exact commutator_commutatorPreimage_le _ _ _ hUA
      have hn : ¬⁅D.UH,c.Ugamma D.Vplus⁆≤D.V₁ := by
        intro hh
        apply hDγ.not_ge
        exact le_commutatorPreimage le_rfl (by rwa [commutator_comm])
      exact place c (quadratic_member_of_common_line s hγH hcardA hc hUgA hn)
  · have hfull := eq_of_le_of_not_lt
      (commutatorPreimage_le (c.Ugamma D.Vplus) D.UH D.V₁) hDγ
    have hn : ⁅D.UH,c.Ugamma D.Vplus⁆≠⊥ :=
      small_spans_not_commute (c.gb:G) h.plus_le
        (le_normalizer_iff_commutator_le_right.mp
          ((geo c).VH_endpoint.trans (c.normalizes_Ugamma D.V))) h47 hbad
    have hc : ⁅D.UH,c.Ugamma D.Vplus⁆≤D.V₁ := by
      rw [commutator_comm]
      conv_lhs => lhs; rw [←hfull]
      exact commutator_commutatorPreimage_le _ _ _
        (hγH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
    have he : ⁅D.UH,c.Ugamma D.Vplus⁆=D.V₁ := by
      have hd : Nat.card (⁅D.UH,c.Ugamma D.Vplus⁆:Subgroup G)∣2 := by
        have hd' := card_dvd_of_le hc
        rw [h.point_card] at hd'
        exact hd'
      have hcard := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
        (fun hz=>hn (card_eq_one.mp hz))
      exact eq_of_le_of_card_ge hc (by rw [hcard,h.point_card])
    let k : G := (c.gb:G)⁻¹
    let A := D.UH.map (MulAut.conj k).toMonoidHom
    let C := D.V₁.map (MulAut.conj k).toMonoidHom
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    have hAH : A≤D.H := AsymmetricPair.return_conjugate_le_H c D.UH
      (huv.trans (geo c).VH_endpoint)
    have hUC : ⁅D.UH,A⁆=C := by
      have hm:=congrArg (fun X:Subgroup G=>X.map (MulAut.conj k).toMonoidHom) he
      rw [map_commutator] at hm
      have hcancel : (c.Ugamma D.Vplus).map (MulAut.conj k).toMonoidHom=D.UH :=
        PairConsequences.conjugate_inverse_cancel (c.gb:G) D.UH
      rw [hcancel,commutator_comm] at hm
      exact hm
    have hCA : A≤centralizer (C:Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      change ⁅D.UH.map _,D.V₁.map _⁆=⊥
      rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr
        (h.UH_le_H.trans h.H_centralizes),Subgroup.map_bot]
    have hCZ : C⊓D.V₁=⊥ := by
      have hm:=congrArg (fun X:Subgroup G=>X.map (MulAut.conj k).toMonoidHom) (geo c).lines_disjoint
      rw [map_inf _ _ _ (MulAut.conj k).injective,Subgroup.map_bot] at hm
      have hh : (c.Aone D.V₁).map (MulAut.conj k).toMonoidHom=D.V₁ :=
        PairConsequences.conjugate_inverse_cancel (c.gb:G) D.V₁
      rwa [hh] at hm
    have hCC : Nat.card C=2 := by rw [card_map_of_injective (MulAut.conj k).injective,h.point_card]
    have hnZ : ¬⁅D.UH,A⁆≤D.V₁ := by
      rw [hUC]
      intro hz
      have heC : C=⊥ := by simpa only [inf_eq_left.mpr hz] using hCZ
      rw [heC,card_bot] at hCC
      omega
    have hplace : A≤(D.LT⊓D.H).pCoreIn 2 := by
      have hc' := map_mono (f:=(MulAut.conj k).toMonoidHom)
        (huv.trans (f9_endpoint_edge_cores D h c hbc).1)
      have hedge : (edgeGroup D.L (D.T:Subgroup G) D.H c.previous c.gamma).map
          (MulAut.conj k).toMonoidHom=D.LT⊓D.H := by
        change (edgeGroup D.L (D.T:Subgroup G) D.H c.previous c.gamma).map
          (MulAut.conj ((c.gb⁻¹ : G0 D.L (D.T:Subgroup G) D.H):G)).toMonoidHom=_
        rw [edgeGroup,map_inf _ _ _ (MulAut.conj _).injective]
        rw [
          ←vertexGroup_smul _ _ _ c.gb⁻¹,←vertexGroup_smul _ _ _ c.gb⁻¹,CriticalPair.previous,
          ←c.gb_zero,←c.gb_one,inv_smul_smul,inv_smul_smul,vertexGroup_base,vertexGroup_base]
        rfl
      rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _
        (MulAut.conj k).injective,hedge] at hc'
      exact hc'
    exact ⟨A,hplace,quadratic_member_of_common_line s hAH hCC hUC.le hCA hnZ⟩

theorem original_witness {T : Sylow 2 G} {Y V ZS Z H : Subgroup G}
    [IsElementaryAbelian 2 V] [IsMulCommutative (conjugateSpanBy V H)]
    [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (h91 : SourceF91 T Y V ZS Z H)
    (h62 : ∀ g:G, V⊓V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (h47 : ∀ x∈centralizer (ZS:Set G),
      ⁅V,zpowers x⁆=⊥ ∨ NormalizingConjugatesCentralize V x)
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z) :
    ∃ B : Subgroup H,
      B≤(((Y⊔(T:Subgroup G))⊓H).pCoreIn 2).subgroupOf H ∧
      IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 H))) ∧
      fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 H)))≤
        2*rank (B.map (QuotientGroup.mk' (pCore 2 H))) := by
  let : IsElementaryAbelian 2 (conjugateSpanBy V H) :=
    conjugateSpanBy_elementary_of_commutative V H
  let : IsElementaryAbelian 2 (f91Setup T Y V ZS Z H).UH :=
    show IsElementaryAbelian 2 (conjugateSpanBy ZS H) from inferInstance
  let : IsElementaryAbelian 2 (f91Setup T Y V ZS Z H).VH :=
    show IsElementaryAbelian 2 (conjugateSpanBy V H) from inferInstance
  obtain ⟨A,hA,hq⟩ := exists_placed_quadratic_member (f91Setup T Y V ZS Z H) h91.toF91
    (conjugationSection a h91.a_centralizes) h62 h47
  exact ⟨A.subgroupOf H,comap_mono hA,hq⟩

/-- The original 15.3.47 and 15.3.62 conclusions discharge the literal
F.9.16(3) input for every quotient action in the Section 15.3 application. -/
theorem original_input {T : Sylow 2 G} {Y V ZS Z H : Subgroup G}
    [IsElementaryAbelian 2 V] [IsMulCommutative (conjugateSpanBy V H)]
    (h62 : ∀ g:G, V⊓V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (h47 : ∀ x∈centralizer (ZS:Set G),
      ⁅V,zpowers x⁆=⊥ ∨ NormalizingConjugatesCentralize V x) :
    F9163Input T Y V ZS Z H := by
  intro hU
  let _ := hU
  intro h98 a
  exact original_witness h98.toSourceF91 h62 h47 a

theorem original_bound {T : Sylow 2 G} {Y V ZS Z H : Subgroup G}
    [IsElementaryAbelian 2 V] [IsMulCommutative (conjugateSpanBy V H)]
    [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (h91 : SourceF91 T Y V ZS Z H)
    (h62 : ∀ g:G, V⊓V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (h47 : ∀ x∈centralizer (ZS:Set G),
      ⁅V,zpowers x⁆=⊥ ∨ NormalizingConjugatesCentralize V x)
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z) :
    quadraticRatio a.representation≤2 := by
  obtain ⟨B,_,hB,hq,hr⟩ := original_witness h91 h62 h47 a
  apply (iInf_le_of_le (B.map (QuotientGroup.mk' (pCore 2 H)))
    (iInf_le_of_le ⟨hB,hq⟩ le_rfl)).trans
  rw [actionRatio,ENNReal.div_le_iff (by exact_mod_cast (ne_of_gt hB.rank_pos)) (by simp)]
  exact_mod_cast hr

theorem original_bounded_action {T : Sylow 2 G} {Y V ZS Z H : Subgroup G}
    [IsElementaryAbelian 2 V] [IsMulCommutative (conjugateSpanBy V H)]
    (h91 : SourceF91 T Y V ZS Z H)
    (h62 : ∀ g:G, V⊓V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    (h47 : ∀ x∈centralizer (ZS:Set G),
      ⁅V,zpowers x⁆=⊥ ∨ NormalizingConjugatesCentralize V x) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy ZS H),
      let _ := hU
      ∃ a : LocalQuotientAction H (conjugateSpanBy ZS H) Z,
        quadraticRatio a.representation≤2 := by
  let hU : IsElementaryAbelian 2 (conjugateSpanBy ZS H) := small_span_elementary h91.zs_le
  let a := localQuotientAction H (conjugateSpanBy ZS H) Z
    (h91.z_lt.le.trans (le_conjugateSpanBy ZS H))
    (conjugateSpanBy_le_self (h91.zs_le.trans (h91.v_le_sylow.trans
      (le_sup_right.trans h91.a_contains))))
    (le_normalizer_conjugateSpanBy ZS H)
    (h91.a_centralizes.trans (Subgroup.centralizer_le_normalizer (Z:Set G)))
    h91.earlier48Conclusions.centralizer_kernel
  exact ⟨hU,a,original_bound h91 h62 h47 a⟩

/-- The original 15.3.64 application, discharging the F.9.16 callback. -/
theorem lemma_15_3_64
    {T : Sylow 2 G} {Y V M Mc ZS Z H : Subgroup G} [IsElementaryAbelian 2 V]
    {z : G} (d : OrthogonalFourBinary.NaturalAction V M)
    (hzV : z∈V) (hz : z≠1) (hzs : d.singular ⟨z,hzV⟩)
    (hZ : Z=zpowers z) (hMc : Mc=centralizer (Z:Set G))
    (hMcFamily : Mc∈sylowOutsideFamily T M)
    (hfusion : ∀a:G, MulAut.conj a z∈V → ∃m∈M, MulAut.conj m z=MulAut.conj a z)
    (hsingular : ∀g:G, g∉M → ∀x:↥(V⊓V.map (MulAut.conj g).toMonoidHom),
      d.singular ⟨x,x.property.1⟩)
    (h47 : ∀x∈centralizer (ZS:Set G), ⁅V,zpowers x⁆=⊥ ∨ NormalizingConjugatesCentralize V x)
    (h48 : ∀J∈sylowOutsideFamily T M, Earlier48Input T Y V ZS Z J)
    (h49 : Y.pCoreIn 2=Y⊓centralizer (V:Set G))
    (h50 : ∀J∈sylowOutsideFamily T M, IsMulCommutative (conjugateSpanBy V J))
    (hH : H∈sylowOutsideFamily T M) :
    ∃hU:IsElementaryAbelian 2 (conjugateSpanBy ZS H), letI:=hU
      ∃a:LocalQuotientAction H (conjugateSpanBy ZS H) Z, quadraticRatio a.representation≤2 := by
  let _ := h50 Mc hMcFamily
  let _ := h50 H hH
  apply original_bounded_action (h48 H hH (Or.inl h49)).toSourceF91
  · exact lemma_15_3_62_2 d hzV hz hzs (by simpa only [hZ] using hMc) hfusion hsingular
  · exact h47


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound.OriginalF916

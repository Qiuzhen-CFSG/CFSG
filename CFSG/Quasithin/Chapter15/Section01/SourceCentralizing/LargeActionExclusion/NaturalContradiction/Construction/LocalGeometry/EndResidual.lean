module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Construction.Flag
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.CubicResidual
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Seed

/-!
# The actual normalized end-node residual

Source 15.1.25 identifies L with O^{3′}(G₁). Intersecting with M_c
identifies O^{3′}(M_L) with O^{3′}(M_Z), which is normalized by T.
The literal binary node residuals are also their prime-to-three residuals;
the nodes other than the first centralize the marked natural point, so
their residuals lie in this same subgroup L₀. Their Sylow supplements
therefore lie in the T-invariant subgroup L₀S.

For the full chosen module, the original central seed lies in the sum
of the two exchanged marked lines. Consequently C_{G₁}(Z)=M_Z, and
the genuine 15.1.14 residual bound gives L₀=O^{3′}(C_G(Z)). No permutation
of the two ends is assumed or asserted here; that orbit and the rank-two
input remain to be constructed.

Source: Aschbacher--Smith, 15.1.25(1), 15.1.28--29, printed pp.1102--1104
of `refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open BinaryLinear.OrderedResidualConjugators
open CFSG.Quasithin.ChapterA.Section05To06
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The source subgroup L₀, with the original ambient embedding. -/
@[expose] def naturalEndResidual (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (primeToResidual 3 d.ML).map d.ML.subtype

/-- Intersecting source 15.1.25 with M_c identifies the literal residual. -/
theorem naturalEndResidual_eq_markedResidual (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource) :
    d.naturalEndResidual = (primeToResidual 3 d.MZ).map d.MZ.subtype := by
  let := hs.1.quasisimple
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  have hL := (d.source_cubic_component hG h
    (facts_of_small_binary_model (small_binary_model_of_marking hn e))).1
  have hh := embedded_primeToResidual_intersection 3 d.G1 Mc
  rw [←hL] at hh
  have he : d.L ⊓ Mc = d.ML := by
    exact le_antisymm (le_inf (le_inf (inf_le_left.trans d.L_component.1) inf_le_right)
      inf_le_left) (le_inf inf_le_right (inf_le_left.trans inf_le_right))
  rw [he] at hh
  exact hh

/-- The source normalization of M_Z passes to its characteristic residual. -/
theorem normalizes_naturalEndResidual (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource) :
    (T : Subgroup G) ≤ normalizer (d.naturalEndResidual : Set G) := by
  rw [d.naturalEndResidual_eq_markedResidual hG h hs]
  exact hs.1.sylow_normalizes_MZ.trans
    (normalizer_le_normalizer_characteristic_image d.MZ (primeToResidual 3 d.MZ))
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- The literal preimage of each node has the same two- and cubic residual. -/
theorem node_twoResidual_eq_cubic (a : NaturalFlag d t) (i : Fin a.m) :
    pResidual 2 (a.node i) = primeToResidual 3 (a.node i) := by
  let P := minimalParabolic a.basis i
  let f : a.node i →* P :=
    (a.action.comp (inclusion (a.node_le i))).codRestrict P (by
      intro x
      have hh := mem_map_of_mem a.action
        (show inclusion (a.node_le i) x ∈ (a.node i).subgroupOf (d.L ⊔ d.S) from x.property)
      rwa [a.node_image] at hh)
  have hf : Function.Surjective f := by
    intro y
    have hy : y.val ∈ ((a.node i).subgroupOf (d.L ⊔ d.S)).map a.action :=
      (a.node_image i).symm ▸ y.property
    obtain ⟨g,hg,he⟩ := hy
    exact ⟨⟨g.val,hg⟩,Subtype.ext he⟩
  have hk : IsPGroup 2 f.ker := by
    have hk : IsPGroup 2 a.action.ker := by
      rw [show a.action.ker = pCore 2 (d.L ⊔ d.S : Subgroup G) from a.kernel]
      exact pCore_isPGroup
    have he : f.ker = a.action.ker.comap (inclusion (a.node_le i)) := by
      ext x
      change f x = 1 ↔ a.action (inclusion (a.node_le i) x) = 1
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_of_injective (inclusion (a.node_le i)) (inclusion_injective (a.node_le i))
  exact twoResidual_eq_primeToResidual_three_of_two_kernel f hf hk
    (minimalParabolic_twoResidual_eq_cubic a.basis i)

/-- The marked point centralizer in LS is exactly the source ML S. -/
theorem marked_point_centralizer (_a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (Z : Subgroup G) (hZS : Z ≤ centralizer (d.S : Set G))
    (hML : d.L ⊓ centralizer (Z : Set G) = d.ML) :
    (d.L ⊔ d.S) ⊓ centralizer (Z : Set G) = d.ML ⊔ d.S := by
  let := hs.1.quasisimple
  obtain ⟨n,hn,⟨e⟩⟩ := hs.2.2
  have hSL := d.S_le_G1.trans (d.G1_normalizes_L hG h
    (facts_of_small_binary_model (small_binary_model_of_marking hn e)))
  have hSC := le_centralizer_iff.mp hZS
  apply le_antisymm
  · rintro g ⟨hg,hgC⟩
    change g ∈ (↑(d.L ⊔ d.S) : Set G) at hg
    rw [coe_mul_of_right_le_normalizer_left d.L d.S hSL] at hg
    obtain ⟨l,hl,s,hss,rfl⟩ := hg
    have hlC : l ∈ centralizer (Z : Set G) := by
      have hh := (centralizer (Z : Set G)).mul_mem hgC
        ((centralizer (Z : Set G)).inv_mem (hSC hss))
      simpa only [mul_inv_cancel_right] using hh
    exact (d.ML ⊔ d.S).mul_mem (mem_sup_left (hML ▸ ⟨hl,hlC⟩)) (mem_sup_right hss)
  · exact sup_le (le_inf (inf_le_right.trans le_sup_left)
      (hML.symm.le.trans inf_le_right)) (le_inf le_sup_right hSC)

/-- Every node other than the first lies in the actual distinguished parabolic. -/
theorem node_le_markedParabolic (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (hnat : d.HasNaturalMovedModule t) (i : Fin a.m) (hi : i.val ≠ 0) :
    a.node i ≤ d.ML ⊔ d.S := by
  obtain ⟨Z,hZU,hcard,hZS,hML,hcut⟩ := a.exists_markedLine hnat
  rw [←a.marked_point_centralizer hG h hs Z hZS hML]
  exact le_inf (a.node_le i)
    ((a.node_normalizes_cut Z hZU i ⟨0,by have := a.dimension; omega⟩
      (by intro hh; exact hi (congrArg Fin.val hh.symm)) hcut).trans
      (normalizer_le_centralizer_of_card_two Z hcard))

/-- The actual end-node residuals lie in the source's T-invariant cubic residual. -/
theorem node_residual_le_endResidual (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnat : d.HasNaturalMovedModule t) (i : Fin a.m) (hi : i.val ≠ 0) :
    (pResidual 2 (a.node i)).map (a.node i).subtype ≤ d.naturalEndResidual := by
  rw [a.node_twoResidual_eq_cubic, d.naturalEndResidual_eq_markedResidual hG h hs]
  apply embedded_primeToResidual_mono
  apply (a.node_le_markedParabolic hG h hs hnat i hi).trans
  have hTMc : (T : Subgroup G) ≤ Mc := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact hMc.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz x hx).symm)
  exact sup_le inf_le_left (le_inf d.S_le_G1 (d.S_le_T.trans hTMc))
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.NaturalFlag

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- In the full source module the original central seed lies in the two
exchanged marked lines, not just in the larger fixed and moving planes. -/
theorem centralInvolutions_le_exchanged_lines (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (s : d.ExchangedSource) (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    centralInvolutions T ≤ d.Z1 ⊔ d.Z2 t := by
  let := h.elementary
  let Z := centralInvolutions T
  let A := d.nineFixedPlane
  let B := d.nineMovingPlane
  have hAV : A ≤ V := le_sup_left.trans_eq s.planes_sup
  have hBV : B ≤ V := le_sup_right.trans_eq s.planes_sup
  have hZ1V : d.Z1 ≤ V := s.marked_le_fixed.trans hAV
  have hZ2B : d.Z2 t ≤ B := by
    exact (map_mono s.marked_le_fixed).trans_eq (s.exchanges t ht htS).1
  have hZ2V : d.Z2 t ≤ V := hZ2B.trans hBV
  have hZV : Z ≤ V := hfull.symm ▸ le_conjugateSpanBy _ _
  have hZA : Z ≤ d.Z1 ⊔ B := (le_inf le_rfl hZV).trans s.seed_bound
  have hZfixed : Z.map (MulAut.conj t).toMonoidHom = Z := by
    apply mem_normalizer_iff_map_conj_eq.mp
    exact (Subgroup.centralizer_le_normalizer (Z : Set G))
      (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hZB : Z ≤ d.Z2 t ⊔ A := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hZA
    rwa [hZfixed,Subgroup.map_sup,(s.exchanges t ht htS).2] at hh
  have hn (X Y : Subgroup G) (hX : X ≤ V) (hY : Y ≤ V) :
      Y ≤ normalizer (X : Set G) :=
    hY.trans (V.le_centralizer.trans ((centralizer_le hX).trans
      (Subgroup.centralizer_le_normalizer _)))
  intro z hz
  have hzA := hZA hz
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ (hn _ _ hZ1V hBV)] at hzA
  obtain ⟨a,ha,b,hb,hab⟩ := hzA
  have hzB := hZB hz
  rw [←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ (hn _ _ hZ2V hAV)] at hzB
  obtain ⟨c,hc,f,hf,hcf⟩ := hzB
  change a * b = z at hab
  change c * f = z at hcf
  have hbc : b * c⁻¹ = a⁻¹ * f := by
    have hcomm : c * f = f * c := (V.le_centralizer (hAV hf)) c (hZ2V hc)
    calc
      b * c⁻¹ = a⁻¹ * (a * b) * c⁻¹ := by group
      _ = a⁻¹ * (c * f) * c⁻¹ := by rw [hab,hcf]
      _ = a⁻¹ * f := by rw [hcomm]; group
  have he : b * c⁻¹ = 1 := by
    apply mem_bot.mp
    rw [←s.planes_inf]
    exact ⟨hbc.symm ▸ A.mul_mem (A.inv_mem (s.marked_le_fixed ha)) hf,
      B.mul_mem hb (B.inv_mem (hZ2B hc))⟩
  have hbc' : b = c := mul_inv_eq_one.mp he
  rw [←hab,hbc']
  exact (d.Z1 ⊔ d.Z2 t).mul_mem (mem_sup_left ha) (mem_sup_right hc)

/-- The original seed centralizer inside G₁ is precisely M_Z. -/
theorem natural_seed_centralizer (d : CaseIComponentData T M Mc V)
    (_hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (s : d.ExchangedSource) (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.G1 ⊓ centralizer (centralInvolutions T : Set G) = d.MZ := by
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  apply le_antisymm (le_inf inf_le_left (inf_le_right.trans hMc.2))
  apply le_inf inf_le_left
  have hC : d.MZ ≤ centralizer ((d.Z1 ⊔ d.Z2 t : Subgroup G) : Set G) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (show d.MZ ≤ centralizer (d.Z1 : Set G) from inf_le_left))
      (le_centralizer_iff.mp (d.exchanged_MZ_le_centralizer_Z2 s t ht))
  exact hC.trans (centralizer_le (d.centralInvolutions_le_exchanged_lines h hfull s t ht htS))

/-- The source's L₀ is the literal global prime-to-three centralizer residual.
Only original 15.1.14(1) remains explicit in this identification. -/
theorem naturalEndResidual_eq_global (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hs : d.HasExchangedLinearSource)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    d.naturalEndResidual = (primeToResidual 3 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype := by
  let C := centralizer (centralInvolutions T : Set G)
  let R := (primeToResidual 3 C).map C.subtype
  have hRC : R ≤ C := map_subtype_le _
  have hRM : R ≤ d.MZ := by
    rw [←d.natural_seed_centralizer hM hu h hfull hs.1 t ht htS]
    exact le_inf ((map_mono primeToResidual_three_le_twoResidual).trans
      (hres.trans (centralizer_le d.Z1_le_fixed))) hRC
  have hid : (primeToResidual 3 R).map R.subtype = R := by
    rw [←map_embedded_primeToResidual_of_hom 3 (primeToResidual 3 C) C.subtype,
      embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 C) le_rfl]
  rw [d.naturalEndResidual_eq_markedResidual hG h hs]
  apply le_antisymm
  · apply embedded_primeToResidual_mono
    rw [←d.natural_seed_centralizer hM hu h hfull hs.1 t ht htS]
    exact inf_le_right
  · have hh := embedded_primeToResidual_mono 3 hRM
    rwa [hid] at hh
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- T normalizes the actual residual--Sylow overgroup of both end nodes. -/
theorem normalizes_naturalEndResidual_sup_sylow (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource) :
    (T : Subgroup G) ≤ normalizer ((d.naturalEndResidual ⊔ d.S : Subgroup G) : Set G) :=
  (le_inf (d.normalizes_naturalEndResidual hG h hs)
    ((normal_subgroupOf_iff_le_normalizer d.S_le_T).mp hs.1.sylow_normal)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

namespace NaturalFlag
variable {d : CaseIComponentData T M Mc V} {t : G}

/-- The two selected end parabolics lie in the same T-invariant residual
extension, with their original residuals contained in L₀ itself. -/
theorem end_nodes_in_residual_extension (a : NaturalFlag d t)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V) (hs : d.HasExchangedLinearSource)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hnat : d.HasNaturalMovedModule t) :
    a.parabolics.Y2 ≤ d.naturalEndResidual ∧
      a.parabolics.Y3 ≤ d.naturalEndResidual ∧
      a.parabolics.P2 ≤ d.naturalEndResidual ⊔ d.S ∧
      a.parabolics.P3 ≤ d.naturalEndResidual ⊔ d.S := by
  have h2 := a.node_residual_le_endResidual hG h hs hu hnat
    ⟨1,by have := a.dimension; omega⟩ (by change (1 : ℕ) ≠ 0; omega)
  have h3 := a.node_residual_le_endResidual hG h hs hu hnat
    ⟨a.m - 1,by have := a.dimension; omega⟩ (by have := a.dimension; dsimp; omega)
  refine ⟨h2,h3,?_,?_⟩
  · rw [a.second_supplement hs.1]
    exact sup_le_sup_right h2 _
  · change a.node _ ≤ _
    rw [a.node_supplement hs.1]
    exact sup_le_sup_right h3 _
end NaturalFlag

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

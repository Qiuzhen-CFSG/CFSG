module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourNilpotent

/-!
# The component-invariant section in the M22-code radical argument

For a parameter-one pair in the actual radical Sylow join, the pair-core
commutator identity gives containment in the join's two-core. The solvable
minimal-parabolic inverter acts on the elementary odd-plane quotient.
The constructed section of O2(X)U/U is invariant under the full containing
component and has dimension at most ten, using |V| = 1024 and |U| = 16.
Both natural and nilpotent A.3.6 alternatives force dimension at least 24.

The Chapter 12 application constructs this pair on the original M22-code
orbit, identifies its fixed space with the original one, and discharges the
radical, H-star, model and cardinal inputs. In particular the faithful
natural action and the possibly nonfaithful nilpotent action remain distinct.
Source: Aschbacher--Smith 8.2.7, printed pp.717--718, using A.3.6 and
B.6.8, refs/quasithin.pdf.
-/


public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter1 Chapter1.Section02 Chapter1.RadicalActions ChapterE
open Section02.Offenders.Parabolic
open Section02.Offenders.Parabolic.Construction Section02.HermitianSource
open Section02.Normalizer.ComponentExclusion Section02.Normalizer.ComponentExclusion.ChiefAction
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem residual_inverter
    {X H V : Subgroup G} {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian p (XiQuotient X)]
    (S : Sylow 2 H) (hmin : ChapterB.IsMinimalParabolicOver S ⊤)
    (hsol : Group.IsSolvable H) (hVH : V ≤ H) (hVS : V.subgroupOf H ≤ S)
    (hSV : (S : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H))
    (hcard : Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2)
    (hX : (pResidual 2 H).map H.subtype = X) :
    ∃ v : V, ∀ x ∈ X, (v : G)*x*(v : G)⁻¹*x ∈ H.pCoreIn 2 := by
  let R := pResidual 2 H
  let e : R ≃* X := (R.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hX)
  let eq := QuotientGroup.congr (pCore 2 R) (pCore 2 X) e (pCore_map_iso 2 e)
  let : IsElementaryAbelian p (R ⧸ pCore 2 R) :=
    IsElementaryAbelian.of_surjective eq.symm.toMonoidHom eq.symm.surjective
  have hc : pCore 2 R = (pCore 2 H).subgroupOf R :=
    pCore_subnormal_eq_comap 2 (inferInstance : R.Normal).isSubnormal
  let eqc := QuotientGroup.quotientMulEquivOfEq hc
  let : IsElementaryAbelian p (R ⧸ (pCore 2 H).subgroupOf R) :=
    IsElementaryAbelian.of_surjective eqc.toMonoidHom eqc.surjective
  let : Fact (IsPGroup p (R ⧸ (pCore 2 H).subgroupOf R)) :=
    ⟨IsElementaryAbelian.isPGroup p _⟩
  have hf : frattini (R ⧸ (pCore 2 H).subgroupOf R) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := p)
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨v,hv,hi⟩ := DihedralCubic.source_residual_frattini_inverter S hmin hsol
    (V.subgroupOf H) hVS (normal_subgroupOf_of_le_normalizer hSV) hcard
  refine ⟨⟨v,hv⟩,?_⟩
  intro x hx
  obtain ⟨r,hr,hrx⟩ := hX.symm ▸ hx
  have hh := hi ⟨r,hr⟩
  change QuotientGroup.mk' ((pCore 2 H).subgroupOf R)
    ((MulAut.conjNormal v : MulAut R) ⟨r,hr⟩ * ⟨r,hr⟩) ∈
      frattini (R ⧸ (pCore 2 H).subgroupOf R) at hh
  rw [hf,mem_bot] at hh
  have hm := (QuotientGroup.eq_one_iff _).mp hh
  refine ⟨v*r*v⁻¹*r,hm,?_⟩
  change (v : G)*(r : G)*(v : G)⁻¹*(r : G) = _
  change (r : G) = x at hrx
  rw [hrx]

/-- The original rank-one pair excludes an elementary odd radical in either
A.3.6 branch. Its section is invariant under the containing component. -/
theorem selected_one_elementary_radical_exclusion
    {κ : GroupClass} {V H M I K U : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 1 i S)
    (h28 : HypothesisE28 κ H T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hT : HypothesisE322 V T) (hE : IsEvenCharacteristicAt T)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hUeq : U = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom)
    (hIC : I ≤ centralizer (U : Set G))
    (hUcard : Nat.card U = 16) (hVcard : Nat.card V = 1024)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p)
    (hXi : XiMember (T : Subgroup G) (XiP p K))
    (hjoin : XiP p K ⊔ (T : Subgroup G) = H)
    [IsElementaryAbelian p (XiQuotient (XiP p K))]
    (hqcard : Nat.card (XiQuotient (XiP p K)) = p^2)
    (hmodel : A36Natural (XiQuotient K) ∨ A36Nilpotent (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) : False := by
  let X := XiP p K
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (hUeq ▸ inf_le_left)
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hq : XiOddQuotient p (XiQuotient X) := Or.inl ⟨inferInstance,hqcard⟩
  have hres : X = (pResidual 2 H).map H.subtype := by
    rw [←hjoin]
    exact (embedded_pResidual_join_pGroup X T hXi.perfect T.isPGroup' hXi.invariant).symm
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hUI : U ≤ I := (hUeq ▸ inf_le_left).trans hVI
  have hUP : U ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 U) hUI (hIC.trans (Subgroup.centralizer_le_normalizer _))
  have hUB : U ≤ V ⊓ I.pCoreIn 2 := le_inf (hUeq ▸ inf_le_left) hUP
  have hP : I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U := by
    rw [hUeq]
    exact selected_one_core_residual_product s
  have hk : (V ⊓ I.pCoreIn 2).relIndex V = 2 := by
    have hr := s.rank_eq
    change rank ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 1 at hr
    rw [quotient_rank_eq_core_corank I V hVI] at hr
    change subgroupCorank V (V ⊓ I.pCoreIn 2) = 1 at hr
    have hh := relIndex_eq_two_pow_quotient_finrank V (V ⊓ I.pCoreIn 2)
    rw [←log_relIndex_eq_quotient_finrank] at hh
    change (V ⊓ I.pCoreIn 2).relIndex V = 2 ^ subgroupCorank V (V ⊓ I.pCoreIn 2) at hh
    simpa only [hr,pow_one] using hh
  have hTH : (T : Subgroup G) ≤ H := h28.le_ambient
  have hSyl : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,map_subgroupOf_eq_of_le hTH⟩
  have hQT := hXi.pCoreIn_le_of_isSylowIn (hSyl.restrict le_sup_right hjoin.le)
  have hcentric := hXi.mem_He (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T hE)
  let : Group.IsSolvable X := hXi.isSolvable
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hsol : Group.IsSolvable H := hjoin ▸ Group.isSolvable_sup_of_normalizes X T hXi.invariant
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [←hjoin]
    exact sup_le ((XiP_le p K).trans hKU) hTU
  have hodd : Odd (Nat.card (XiQuotient X)) := by rw [hqcard]; exact ho.pow
  have hcore := pair_core_le I H X U s.family.le_ambient hres hUI
    (IsElementaryAbelian.isPGroup 2 U) hHU hodd hP
  obtain ⟨S₂,hS₂,hmin,_⟩ := h28.minimal
  have hVS : V.subgroupOf H ≤ S₂ := by rw [hS₂]; exact comap_mono hT.le_sylow
  have hSV : (S₂ : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H) := by
    rw [hS₂,←subgroupOf_normalizer_eq (hT.le_sylow.trans hTH)]
    exact comap_mono hT.normalizes
  have hVcardH : Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 := by
    rw [←relIndex_ker,QuotientGroup.ker_mk']
    have hQ : (H.pCoreIn 2).subgroupOf H = pCore 2 H := by
      exact comap_map_eq_self_of_injective H.subtype_injective _
    rw [←hQ,relIndex_subgroupOf (hT.le_sylow.trans hTH),←inf_relIndex_right]
    rw [inf_comm (H.pCoreIn 2) V,←pair_core_intersection I H V s.family.le_ambient hVI hcore]
    exact hk
  obtain ⟨v,hinv⟩ := residual_inverter (p := p) S₂ hmin hsol (hT.le_sylow.trans hTH)
    hVS hSV hVcardH hres.symm
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := X)
  let Y := (P : Subgroup X).map X.subtype
  let eY := hXi.ambientSylowQuotientEquiv ho hq P
  let : IsElementaryAbelian p Y := IsElementaryAbelian.of_surjective eY.symm.toMonoidHom eY.symm.surjective
  have hYcard : Nat.card Y = p^2 := (Nat.card_congr eY.toEquiv).trans hqcard
  obtain ⟨hJR,D,hUD,hDR,hJD,hN,ρ,hρ,helem,hne,hirr,hfull,hactive,_hker,hsmall⟩ :=
    exists_bounded_component_section p hp K U V T Y H I hTK hKU hTU hQT
      ((hUeq ▸ inf_le_left).trans hT.le_sylow) T.isPGroup' (map_subtype_le _) P rfl hYcard
      hq.isPGroup hcentric hres (selected_generates_hstar s hH) hIC
      hVI hT.le_sylow hT.normalizes hUB hk hUcard (Or.inr hVcard) v
      (fun y hy => hinv y ((map_subtype_le _) hy))
  let := hN
  let := helem
  let := hne
  rcases hmodel with hnat | hnil
  · obtain ⟨_,E,hE,eq,N,hN',_hmark,helN,hNcard,hnatural,_⟩ :=
      ExtensionImage.natural_extension_of_component_section p K T Y hTK
        (map_subtype_le _) ρ hirr hactive hnat hd
    let := hN'
    let := helN
    exact oddPlaneExtension_section_obstruction N hp hNcard (Or.inl hnatural)
      ρ.range (inclusion hE) (inclusion_injective hE) hsmall
  · have hKperfect : Group.IsPerfect K := by
      let e : K.subgroupOf (K ⊔ (T : Subgroup G)) ≃* K := subgroupOfEquivOfLe le_sup_left
      let := hK.1.perfect
      exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let := hKperfect
    let : Group.IsPerfect (XiQuotient K) := Group.IsPerfect.ofSurjective
      (f := QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
    let eq := xiPQuotientEquivCore ho K
    let : IsElementaryAbelian p (omegaCore p (XiQuotient K)) :=
      IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective
    have hQker := core_killed (K ⊔ (T : Subgroup G)) K ρ (sup_le K.le_normalizer hTK) hirr
    let τ := ExtensionImage.componentQuotientAction (K ⊔ (T : Subgroup G)) K le_sup_left ρ hQker
    have hact := ExtensionImage.omega_active p (K ⊔ (T : Subgroup G)) K Y le_sup_left
      (map_subtype_le _) ρ hQker hactive
    have hlarge := nilpotent_omega_plane_degree hnil p hd τ hact
    omega

end CFSG.Quasithin.Chapter8.MathieuShadowRows

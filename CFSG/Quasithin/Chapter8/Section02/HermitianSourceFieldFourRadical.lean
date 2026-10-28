module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourMovement
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.ExtensionImage
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.AffineDegree
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.QuotientShape
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.ResidualInverter
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.NormalizedSupConsequences
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Assembly
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# The natural radical alternative at a Hermitian selected pair

For a local component K with the natural A.3.6 quotient, its actual radical
X = Ξ_p(K) belongs to Ξ(G,T). At a parameter-one Hermitian pair inside
H = XT, the saved core movement identity places the pair core in O₂(H).
The image of V in H/O₂(H) has order two. The solvable minimal-parabolic
Frattini inverter therefore inverts the elementary odd-plane quotient.

The component-invariant section of O₂(X)U/U has binary dimension at most
ten. On that same section the natural quotient of K acts faithfully;
its odd-plane extension requires dimension at least twenty-four. This
excludes the natural A.3.6 branch at the original selected pair.

The Chapter 12 companion constructs the radical's selected pair on the
actual tensor. Radical H-star placement and the nilpotent A.3.6 alternative
remain necessary for the full 8.2.7 theorem. This is not yet the field-four
exclusion through 8.2.13.
Source: Aschbacher--Smith A.3.6, 1.3.3 and 8.2.7, printed pp.43--45,
509,717--718, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open Chapter1 Chapter1.Section02 ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open Normalizer.ComponentExclusion Normalizer.ComponentExclusion.ChiefAction
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem natural_radical_quotient (p : ℕ) [Fact p.Prime] (K : Subgroup G)
    (hnat : A36Natural (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) :
    3 < p ∧ IsElementaryAbelian p (XiQuotient (XiP p K)) ∧
      Nat.card (XiQuotient (XiP p K)) = p^2 := by
  obtain ⟨hp,he,hc⟩ := RadicalStructure.natural_core hnat hd
  let := he
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have ht : omega (pCore p (XiQuotient K)) (p := p) 1 = ⊤ := RadicalStructure.omega_top
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (pCore p (XiQuotient K))))
  let e := (xiPQuotientEquivOmega ho K).trans ((MulEquiv.subgroupCongr ht).trans topEquiv)
  exact ⟨hp,IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective,
    (Nat.card_congr e.toEquiv).trans hc⟩

/-- A natural local quotient gives the actual radical in the source Ξ-family. -/
theorem natural_radical_member {κ : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK κ E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
        C.IsCComponent → A36Conclusion C)
    {T K : Subgroup G} (hK : K ∈ Chapter1.L G T)
    (hQ : IsSQTK κ ((K ⊔ T : Subgroup G) ⧸ pCore 2 (K ⊔ T : Subgroup G)))
    (hTK : T ≤ normalizer (K : Set G))
    (p : ℕ) [Fact p.Prime] (hnat : A36Natural (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) :
    XiMember T (XiP p K) := by
  have hn : ¬ IsQuasisimple (XiQuotient K) := by
    intro hq
    let := hq
    have hf : fittingSubgroup (XiQuotient K) = ⊤ :=
      hnat.1.symm.trans generalizedFitting_eq_top_of_quasisimple
    let e := (MulEquiv.subgroupCongr hf).trans topEquiv
    let : IsSimpleGroup (XiQuotient K ⧸ center (XiQuotient K)) := IsQuasisimple.simple
    let : Nontrivial (XiQuotient K) := Function.Surjective.nontrivial
      (QuotientGroup.mk'_surjective (center (XiQuotient K)))
    exact Group.IsPerfect.not_isSolvable (XiQuotient K)
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  obtain ⟨hp,hel,hcard⟩ := natural_radical_quotient p K hnat hd
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  exact ⟨XiP_isPPerfect p K,XiP_invariant p hTK,XiP_join_mem_H p hK,
    ⟨p,Fact.out,ho,Or.inl ⟨hel,hcard⟩⟩,
    RadicalActions.XiP_irreducible_of_A36 hA36 hK hQ hn hTK ho hd⟩

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

/-- The natural odd-plane alternative cannot occur at a reselected Hermitian
pair in the radical's actual Sylow join. -/
theorem selected_one_natural_radical_exclusion
    {κ : GroupClass} {V H M I K : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} {i : I} {S : Sylow 2 I}
    (s : Selected H T M V I 1 i S)
    (h28 : HypothesisE28 κ H T M V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hT : HypothesisE322 V T) (hE : IsEvenCharacteristicAt T)
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (j : Automizer V →* binaryNormalizer 1) (hj : Function.Injective j)
    (he : ∀ a v, e (automizerRepresentation V a v) =
      overgroupAction 1 (binaryNormalizer 1) (j a) (e v))
    (p : ℕ) [Fact p.Prime]
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK κ E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
        C.IsCComponent → A36Conclusion C)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hQ : IsSQTK κ ((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)))
    (hjoin : XiP p K ⊔ (T : Subgroup G) = H)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKU : K ≤ normalizer
      (V ⊓ centralizer (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G))
    (hnat : A36Natural (XiQuotient K))
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient K))) : False := by
  have hXi := natural_radical_member hA36 hK hQ hTK p hnat hd
  let X := XiP p K
  let A := V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let U := V ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ V from inf_le_left)
  obtain ⟨hp,hel,hqcard⟩ := natural_radical_quotient p K hnat hd
  let := hel
  have ho : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  have hq : XiOddQuotient p (XiQuotient X) := Or.inl ⟨hel,hqcard⟩
  have hres : X = (pResidual 2 H).map H.subtype := by
    rw [←hjoin]
    exact (embedded_pResidual_join_pGroup X T hXi.perfect T.isPGroup' hXi.invariant).symm
  let : Group.IsSolvable X := hXi.isSolvable
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  have hsol : Group.IsSolvable H := hjoin ▸ Group.isSolvable_sup_of_normalizes X T hXi.invariant
  have hTH : (T : Subgroup G) ≤ H := hjoin ▸ le_sup_right
  have hSyl : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH,map_subgroupOf_eq_of_le hTH⟩
  have hQT := hXi.pCoreIn_le_of_isSylowIn (hSyl.restrict le_sup_right hjoin.le)
  have hcentric := hXi.mem_He (fun _ hM _ hN hNM hn => lemma_1_1_3_1 hM hN hNM hn)
    (lemma_1_1_4_6 T hE)
  obtain ⟨_,_,_,hu,hUeq,_,hTU,hIC,_,_⟩ := selected_one_fixed_subgroup s hT 1 e j hj he
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  have hUI : U ≤ I := inf_le_left.trans hVI
  have hU2 : IsPGroup 2 U := IsElementaryAbelian.isPGroup 2 U
  have hUP : U ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes hU2 hUI
    (hIC.trans (Subgroup.centralizer_le_normalizer _))
  have hUB : U ≤ V ⊓ I.pCoreIn 2 := le_inf inf_le_left hUP
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [←hjoin]
    exact sup_le ((XiP_le p K).trans hKU) hTU
  have hP : I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U := by
    exact (selected_one_core_residual_product s).trans
      (congrArg (fun Z => ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ Z) hUeq.symm)
  have hodd : Odd (Nat.card (XiQuotient X)) := by rw [hqcard]; exact ho.pow
  have hcore := pair_core_le I H X U s.family.le_ambient hres hUI hU2 hHU hodd hP
  have hk : (V ⊓ I.pCoreIn 2).relIndex V = 2 := by
    have hr := s.rank_eq
    change rank ((V.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 1 at hr
    rw [quotient_rank_eq_core_corank I V hVI] at hr
    change subgroupCorank V (V ⊓ I.pCoreIn 2) = 1 at hr
    have hh := relIndex_eq_two_pow_quotient_finrank V (V ⊓ I.pCoreIn 2)
    rw [←log_relIndex_eq_quotient_finrank] at hh
    change (V ⊓ I.pCoreIn 2).relIndex V = 2 ^ subgroupCorank V (V ⊓ I.pCoreIn 2) at hh
    simpa only [hr,pow_one] using hh
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
  have hUcard : Nat.card U = 16 := by
    obtain ⟨a,ha⟩ := hU2.exists_card_eq
    change rank U = 4 at hu
    rw [rank,ha,Nat.log_pow Nat.one_lt_two] at hu
    simpa [hu] using ha
  have hVcard : Nat.card V = 512 := by
    change Nat.card (Additive V) = 512
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,e.finrank_eq,finrank_binary]
    norm_num
  obtain ⟨hJR,D,hUD,hDR,hJD,hN,ρ,hρ,helem,hne,hirr,hfull,hactive,_hker,hsmall⟩ :=
    exists_bounded_component_section p hp K U V T Y H I hTK hKU hTU hQT
      (inf_le_left.trans hT.le_sylow) T.isPGroup' (map_subtype_le _) P rfl hYcard
      hq.isPGroup hcentric hres (selected_generates_hstar s hH) hIC
      hVI hT.le_sylow hT.normalizes hUB hk hUcard (Or.inl hVcard) v
      (fun y hy => hinv y ((map_subtype_le _) hy))
  let := hN
  let := helem
  let := hne
  obtain ⟨_,E,hE,eq,N,hN',_hmark,helN,hNcard,hnatural,_⟩ :=
    ExtensionImage.natural_extension_of_component_section p K T Y hTK
      (map_subtype_le _) ρ hirr hactive hnat hd
  let := hN'
  let := helN
  exact oddPlaneExtension_section_obstruction N hp hNcard (Or.inl hnatural)
    ρ.range (inclusion hE) (inclusion_injective hE) hsmall

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticQuarticCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSwapContainment
-- Internal proof split: reuse cyclic restriction uniqueness from the preceding support calculation.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSwapCore

/-!
# Actual alternatives for the original quintic partner core

If the original module is not already in the partner two-core, no core
element exchanges the two supports or has order-four action on a support.
Each core element therefore acts as an involution on the original module.
Cyclic support action identifies its restriction with a genuine elementary
Thompson generator, so it centralizes E. Ambient representatives need not
be involutions. The full partner-kernel span of E is then central in Q.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem image_involution_centralizes_fixed
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T:Subgroup G)≤M) (hn : M≤normalizer (V:Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T:=T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀g k,(c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom=
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀g k,(c.ambientFactor d k).space.map (imageRepresentation M V hn g)=
      (c.ambientFactor d (π g k)).space)
    (hfive : s.prime=5) (a:G) (haT:a∈(T:Subgroup G))
    (ha2:a^2∈centralizer (V:Set G))
    (haN:a∈normalizer (plane V (c.ambientFactor d s.first).space:Set G)) :
    a∈centralizer (thompsonFixed T V:Set G) := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M→*D := (actionHom M V hn).rangeRestrict
  let S : Subgroup D := ((T:Subgroup G).subgroupOf M).map f
  let J := ChapterB.thompsonJ (T:Subgroup G) 1
  let a₀ : M := ⟨a,hTM haT⟩
  have haD2 : (f a₀)^2=1 := by
    rw [←map_pow]
    apply Subtype.ext
    change actionHom M V hn (a₀^2)=1
    exact (show a₀^2∈(actionHom M V hn).ker from (actionHom_ker M V hn).symm ▸ ha2)
  have hJN : J≤normalizer (plane V (c.ambientFactor d s.first).space:Set G) := by
    intro j hj
    apply s.centralizer_le_stabilizer
    exact ⟨ChapterB.thompsonJ_le _ _ hj,fun z hz => (hz.2.2 j hj).symm⟩
  have hNk (x:G) (hxT:x∈(T:Subgroup G))
      (hxN:x∈normalizer (plane V (c.ambientFactor d s.first).space:Set G)) (k:d.Index) :
      x∈normalizer (plane V (c.ambientFactor d k).space:Set G) := by
    rcases s.covers k with hk | hk
    · simpa only [hk] using hxN
    · simpa only [hk] using s.stabilizes_second ⟨hxT,hxN⟩
  have hfix (k:d.Index) : a∈centralizer (thompsonPlane T V (c.ambientFactor d k).space:Set G) := by
    let F := c.ambientFactor d k
    let Vi := plane V F.space
    let Zi := thompsonPlane T V F.space
    let R := S⊓subspaceStabilizer ρ F.space
    have hstab (x:M) (hx:(x:G)∈normalizer (Vi:Set G)) : f x∈subspaceStabilizer ρ F.space := by
      apply (subspace_map_eq_iff ρ F.space (f x)).mp
      apply plane_injective V
      exact (plane_conjugate hn F.space x).symm.trans (mem_normalizer_iff_map_conj_eq.mp hx)
    have haR : f a₀∈R := ⟨mem_map_of_mem f haT,hstab a₀ (hNk a haT haN k)⟩
    let : IsCyclic (restrictedSubgroup ρ F.space R) := quintic_support_two_cyclic F
      (c.support_stabilizer_normalizes_actor d π hp hs k) (s.marking k)
      (by change CyclicSource.DihedralMarking (s.marking k) 5 2; simpa only [hfive] using s.dihedral k)
      R ((T.isPGroup'.comap_subtype).map f).to_inf_left inf_le_right
    have hnJ : ¬J≤centralizer (Vi:Set G) := by
      intro hc
      have hViZ : Vi≤Zi := le_inf le_rfl
        (le_inf (plane_le _) (le_centralizer_iff.mp hc))
      have hh := card_le_of_le hViZ
      rw [s.support_card k,s.thompson_card k] at hh
      omega
    have hnFam : ¬∀H∈ChapterB.thompsonFamily (T:Subgroup G) 1,H≤centralizer (Vi:Set G) := by
      intro hh
      exact hnJ (sSup_le hh)
    push Not at hnFam
    obtain ⟨H,hH,hHC⟩ := hnFam
    obtain ⟨b,hb,hbC⟩ := Set.not_subset.mp hHC
    let : IsElementaryAbelian 2 H := hH.2.1
    have hbJ : b∈J := le_sSup hH hb
    have hbT : b∈(T:Subgroup G) := hH.1 hb
    let b₀ : M := ⟨b,hTM hbT⟩
    have hbR : f b₀∈R := ⟨mem_map_of_mem f hbT,hstab b₀ (hNk b hbT (hJN hbJ) k)⟩
    have hbD2 : (f b₀)^2=1 := by
      rw [←map_pow,show b₀^2=1 from Subtype.ext
        (elemPow_eq_one_of_isElementaryAbelian (p:=2) b hb),map_one]
    have hne : ¬∀v∈F.space,ρ (f b₀) v=v := by
      intro hh
      apply hbC
      rintro v ⟨w,hw,rfl⟩
      have he := congrArg (fun v:Additive V => (v.toMul:G)) (hh _ hw)
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    rintro z ⟨hzF,hzE⟩
    obtain ⟨w,hw,rfl⟩ := hzF
    have hwb : ρ (f b₀) (Additive.ofMul w)=Additive.ofMul w := by
      apply Subtype.ext
      change b*(w:G)*b⁻¹=(w:G)
      have hh : b*(w:G)=(w:G)*b := hzE.2 b hbJ
      rw [hh,mul_inv_cancel_right]
    have hwa := cyclic_restriction_fixed_mono ρ F.space R inf_le_right
      (f b₀) hbR hbD2 hne (f a₀) haR haD2 (Additive.ofMul w) hw hwb
    have he := congrArg (fun v:Additive V => (v.toMul:G)) hwa
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hh : thompsonFixed T V≤centralizer ({a}:Set G) := by
    rw [s.thompson_split]
    exact sup_le (fun z hz => mem_centralizer_singleton_iff.mpr (hfix s.first z hz))
      (fun z hz => mem_centralizer_singleton_iff.mpr (hfix s.second z hz))
  intro z hz
  exact mem_centralizer_singleton_iff.mp (hh hz)

/-- The actual original module is in the partner core, or that core fixes
E and its full partner-kernel span is central in the core. -/
theorem PreparedChosenModule.decomposable_five_partner_core_alternatives
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
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc:Set G)
      let Q := Mc.pCoreIn 2
      let F := conjugateSpanBy E C
      V≤Q ∨ (Q≤centralizer (E:Set G) ∧ F≤Q⊓centralizer (Q:Set G) ∧ E≤F ∧
        ⁅V,Q⁆≤E ∧ ⁅V,F⁆≤E ∧ V≤centralizer (E:Set G)) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc:Set G)
  let Q := Mc.pCoreIn 2
  let F := conjugateSpanBy E C
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  by_cases hVQ : V≤Q
  · exact Or.inl hVQ
  right
  obtain ⟨hCMc,hcore,hQT,_,hself,hEC,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hQT' : Q≤(T:Subgroup G) := by
    change Mc.pCoreIn 2≤(T:Subgroup G)
    rw [←hcore]
    exact hQT
  have hQN : Mc≤normalizer (Q:Set G) := Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hCQ : C≤normalizer (Q:Set G) := hCMc.trans hQN
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTQ : (T:Subgroup G)≤normalizer (Q:Set G) := hTMc.trans hQN
  have hstable (q:G) (hqQ:q∈Q) : q∈normalizer (V₁:Set G) := by
    by_contra hn
    exact hVQ (h.decomposable_five_partner_core_exchange_forces_module
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive q hqQ hn)
  have hsquare (q:G) (hqQ:q∈Q) : q^2∈centralizer (V₁:Set G) := by
    by_contra hn
    exact hVQ (h.decomposable_five_partner_core_quartic_forces_module
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive q hqQ (hstable q hqQ) hn)
  let S₀ := (T:Subgroup G)⊓normalizer (V₁:Set G)
  have hSne : S₀≠(T:Subgroup G) := by
    intro he
    have hi : S₀.relIndex (T:Subgroup G)=2 := s.stabilizer_index
    rw [he,relIndex_self] at hi
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt (lt_of_le_of_ne (show S₀≤(T:Subgroup G) from inf_le_left) hSne)
  have htex : V₁.map (MulAut.conj t).toMonoidHom=V₂ :=
    (s.exchanges t ht (fun hh => htS ⟨ht,hh⟩)).1
  have hsquareV (q:G) (hqQ:q∈Q) : q^2∈centralizer (V:Set G) := by
    have hc₁ := hsquare q hqQ
    have hc₂ : q^2∈centralizer (V₂:Set G) := by
      let q' := t⁻¹*q*t
      have hq' : q'∈Q := by
        have hh := le_normalizer_iff.mp hTQ t⁻¹ ((T:Subgroup G).inv_mem ht) q hqQ
        simpa only [inv_inv] using hh
      rintro v hv
      rw [←htex] at hv
      obtain ⟨u,hu,rfl⟩ := hv
      have hh := congrArg (MulAut.conj t) (hsquare q' hq' u hu)
      have he : MulAut.conj t q'=q := by simp [q',MulAut.conj_apply,mul_assoc]
      change MulAut.conj t u * q^2 = q^2 * MulAut.conj t u
      simpa only [map_mul,map_pow,he] using hh
    have hh : V≤centralizer ({q^2}:Set G) := by
      rw [←s.complement]
      exact sup_le (fun v hv => mem_centralizer_singleton_iff.mpr (hc₁ v hv))
        (fun v hv => mem_centralizer_singleton_iff.mpr (hc₂ v hv))
    intro v hv
    exact mem_centralizer_singleton_iff.mp (hh hv)
  have hQE : Q≤centralizer (E:Set G) := by
    intro q hqQ
    exact image_involution_centralizes_fixed hM.1.2 h.normalized c d s π hp hs hfive
      q (hQT' hqQ) (hsquareV q hqQ) (hstable q hqQ)
  have hFQcentral : F≤centralizer (Q:Set G) := conjugateSpanBy_le
    (le_centralizer_iff.mp hQE) (hCQ.trans (normalizer_le_normalizer_centralizer _))
  have hFC : F≤C := conjugateSpanBy_le hEC C.le_normalizer
  have hFQ : F≤Q := by
    have hh : C⊓centralizer (Q:Set G)≤Q := by
      change centralizer (localModule T Mc:Set G)⊓centralizer (Mc.pCoreIn 2:Set G)≤Mc.pCoreIn 2
      rw [←hcore]
      exact hself
    exact (le_inf hFC hFQcentral).trans hh
  have hmove : ⁅V,Q⁆≤E := by
    rw [commutator_comm]
    exact (commutator_mono (le_inf hQT' hQE) le_rfl).trans
      (h.decomposable_five_fixed_centralizer_displacement
        hG T hempty hM hmany hJ hfull c d hd s π hp hs hdec hq hfive)
  exact ⟨hQE,le_inf hFQ hFQcentral,le_conjugateSpanBy E C,hmove,
    (commutator_mono le_rfl hFQ).trans hmove,
    V.le_centralizer.trans (centralizer_le inf_le_left)⟩

end CFSG.Quasithin.Chapter15.Section01

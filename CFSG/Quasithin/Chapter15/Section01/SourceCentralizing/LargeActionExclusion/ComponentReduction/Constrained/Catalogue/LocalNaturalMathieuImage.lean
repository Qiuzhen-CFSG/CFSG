module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalOrdinary
public import Theory.Mathieu.M22.Properties.LocalA5Shape
public import Theory.Mathieu.M23.Properties.NoOrderTen

/-!
# Full natural local images in the two remaining Mathieu carriers

For a natural local escape, the original selected component has central
quotient M₂₂ or M₂₃. Its literal local image has an A₅ quotient and a nonzero
two-core whose order divides 32. An element of order five acts freely on
this core: otherwise it fixes an involution, contradicting the native
involution-centralizer order. The free-action theorem makes the core
elementary of order sixteen.

The natural module survives the central cover with order sixteen. Thus
its full commutator layer equals the image two-core and has no fixed
attachment. The A₅ quotient then makes the entire image centerless, of
order 960. Consequently the kernel of the original member's restriction
is exactly its center. The original moving plane is disjoint from this
kernel by the proved fixed/moving decomposition, so its same four-group
embeds in the carrier quotient. The image of the full original U-layer is
also retained explicitly; no central attachment of the original cover is
silently removed.

The original-marker consumer uses the same component, prime, planes and
quotient map. These image calculations do not exclude either embedding or
establish Borel containment. Those ambient steps and final 15.1.20(2) and
15.1.22 assembly remain open; original 15.1.14 and whole-core A₆
reconstruction retain their existing producers.

Source: Aschbacher--Smith 15.1.20(2), 15.1.22, printed pp.1094--1100;
A.3.12(12), A.3.14(6), pp.47--49, for the local Mathieu sections.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

private theorem small_core_shape
    {H : Type*} [Group H] [Finite H] (D : Subgroup H)
    (e : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 5))
    (hc : pCore 2 D ≠ ⊥) {m : ℕ} (hm : Odd m)
    (hH : Nat.card H = 60 * (32 * m))
    (hfive : ∀ t : H, orderOf t = 2 →
      ¬ 5 ∣ Nat.card (centralizer ({t} : Set H))) :
    IsElementaryAbelian 2 (pCore 2 D) ∧ Nat.card (pCore 2 D) = 16 := by
  have hq : Nat.card (D ⧸ pCore 2 D) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num
  have hd : Nat.card (pCore 2 D) ∣ 32 := by
    have hd := D.card_subgroup_dvd_card
    rw [hH,card_eq_card_quotient_mul_card_subgroup (pCore 2 D),hq] at hd
    have hd' : Nat.card (pCore 2 D) ∣ 32 * m :=
      (Nat.mul_dvd_mul_iff_left (by decide : 0 < 60)).mp hd
    have hcop : Nat.Coprime (Nat.card (pCore 2 D)) m := by
      obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
      rw [hn]
      exact hm.coprime_two_left.pow_left n
    exact hcop.dvd_of_dvd_mul_right hd'
  have h5 := (show 5 ∣ Nat.card (D ⧸ pCore 2 D) by rw [hq]; decide).trans
    (card_quotient_dvd_card (pCore 2 D))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := D) 5 h5
  let a : MulAut (pCore 2 D) := MulAut.conjNormal b
  have ha : a ^ 5 = 1 := by
    change (MulAut.conjNormal b : MulAut (pCore 2 D)) ^ 5 = 1
    have hp : b ^ 5 = 1 := by rw [←hb]; exact pow_orderOf_eq_one b
    rw [←map_pow,hp,map_one]
  have hf : MonoidHom.FixedPointFree a := by
    apply (pCore_isPGroup (p := 2) (G := D)).fixedPointFree_of_no_fixed_prime_order
    intro x hx hfix
    have hxH : orderOf (x.val.val : H) = 2 := by
      rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe,hx]
    let c : centralizer ({x.val.val} : Set H) := ⟨b.val,by
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun y : pCore 2 D => y.val.val) hfix
      change b.val * x.val.val * b.val⁻¹ = x.val.val at he
      exact mul_inv_eq_iff_eq_mul.mp he⟩
    have hc : orderOf c = 5 :=
      (Subgroup.orderOf_coe c).symm.trans ((Subgroup.orderOf_coe b).trans hb)
    exact hfive _ hxH (hc ▸ orderOf_dvd_natCard c)
  exact (elementary_sixteen_of_free_five_small_core pCore_isPGroup hd a ha hf).resolve_left
    (fun h1 => hc (card_eq_one.mp h1))

private theorem mathieu_core_shape
    {H : Type*} [Group H] [Finite H] (D : Subgroup H)
    (e : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 5))
    (hc : pCore 2 D ≠ ⊥)
    (model : Nonempty (H ≃* Sporadic.Mathieu.M22) ∨ Nonempty (H ≃* Sporadic.Mathieu.M23)) :
    IsElementaryAbelian 2 (pCore 2 D) ∧ Nat.card (pCore 2 D) = 16 := by
  have transfer {J : Type} [Group J] [Finite J] (f : H ≃* J)
      (hj : ∀ t : J, orderOf t = 2 → ¬ 5 ∣ Nat.card (centralizer ({t} : Set J))) :
      ∀ t : H, orderOf t = 2 → ¬ 5 ∣ Nat.card (centralizer ({t} : Set H)) := by
    intro t ht hd
    have he : (centralizer ({t} : Set H)).map f.toMonoidHom =
        centralizer ({f t} : Set J) := by
      rw [map_centralizer_equiv ({t} : Set H) f,Set.image_singleton]
    apply hj (f t) ((f.orderOf_eq t).trans ht)
    rwa [←he,card_map_of_injective f.injective]
  rcases model with hf | hf <;> obtain ⟨f⟩ := hf
  · apply small_core_shape D e hc (m := 231) (by decide)
    · rw [Nat.card_congr f.toEquiv,Sporadic.Mathieu.m22_order]
    · apply transfer f
      intro t ht
      rw [Sporadic.Mathieu.M22FourNormalizers.involution_centralizer_card t ht]
      decide
  · apply small_core_shape D e hc (m := 5313) (by decide)
    · rw [Nat.card_congr f.toEquiv,Sporadic.Mathieu.m23_order]
    · exact transfer f Sporadic.Mathieu.m23_involution_centralizer_not_five

private theorem natural_mathieu_image
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    (q : A →* H) (hp : IsPGroup 2 q.ker) (hz : q.ker ≤ center A)
    (B : Subgroup A) (hb : IsL2EvenBlock B 2)
    (model : Nonempty (H ≃* Sporadic.Mathieu.M22) ∨ Nonempty (H ≃* Sporadic.Mathieu.M23)) :
    let D := B.map q
    IsElementaryAbelian 2 (pCore 2 D) ∧ Nat.card (pCore 2 D) = 16 ∧
      blockU D = pCore 2 D ∧ blockFixed D = ⊥ ∧ center D = ⊥ ∧
      Nat.card D = 960 ∧ (blockU B).map (q.subgroupMap B) = blockU D ∧
      (q.subgroupMap B).ker = center B := by
  intro D
  let f := q.subgroupMap B
  have hf : Function.Surjective f := q.subgroupMap_surjective B
  have hfp : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact hp.comap_subtype
  have hfc : f.ker ≤ center B := by
    intro b hb
    have hzb : (b : A) ∈ center A := hz (congrArg Subtype.val (MonoidHom.mem_ker.mp hb))
    exact mem_center_iff.mpr (fun a => Subtype.ext (mem_center_iff.mp hzb a))
  have hU : (blockU B).map f = blockU D := by
    have hc : (pCore 2 B).map f = pCore 2 D := by
      rw [←f.comap_pCore_of_ker_isPGroup hf hfp,map_comap_eq_self_of_surjective hf]
    rw [blockU,map_commutator,hc,map_top_of_surjective _ hf]
    rfl
  have hm : Nat.card (BlockModule D) = 16 := by
    obtain ⟨F,hF,hfin,hcard,_,ρ,⟨m⟩,hρ⟩ := hb.2.2
    obtain ⟨m'⟩ := m.exists_of_central_two_quotient f hf hb.2.1.twoPerfect hfp hfc ρ
    rw [Nat.card_congr m'.moduleIso.toEquiv]
    change Nat.card (Fin 2 → F) = 16
    rw [Nat.card_fun,Nat.card_fin,hcard]
    norm_num
  have hsize : 16 ≤ Nat.card (blockU D) := by
    rw [←hm]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (blockFixed D))
      (QuotientGroup.mk'_surjective _)
  let e := (f.pCoreQuotientEquiv hf hfp).symm.trans hb.four_quotient_alternatingFive.some
  have hne : pCore 2 D ≠ ⊥ := by
    intro hc
    have hu : blockU D = ⊥ := bot_unique (blockU_le_core.trans hc.le)
    rw [hu,card_bot] at hsize
    omega
  obtain ⟨hE,h16⟩ := mathieu_core_shape D e hne model
  have hUD : blockU D = pCore 2 D := eq_of_le_of_card_ge blockU_le_core (by omega)
  have hfixed : blockFixed D = ⊥ := by
    have hc := card_eq_card_quotient_mul_card_subgroup (blockFixed D)
    change Nat.card (blockU D) = Nat.card (BlockModule D) * Nat.card (blockFixed D) at hc
    have hU16 : Nat.card (blockU D) = 16 := (congrArg (fun E : Subgroup D => Nat.card E) hUD).trans h16
    rw [hU16,hm] at hc
    exact card_eq_one.mp (by omega)
  have hcenter : center D = ⊥ := by
    apply bot_unique
    intro x hx
    have hxcore : x ∈ pCore 2 D := by
      let g := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
      have hg : Function.Surjective g := e.surjective.comp (QuotientGroup.mk'_surjective _)
      have hgz : g x ∈ center (alternatingGroup (Fin 5)) := by
        apply mem_center_iff.mpr
        intro y
        obtain ⟨z,rfl⟩ := hg y
        simpa only [map_mul] using congrArg g (mem_center_iff.mp hx z)
      rw [alternatingGroup.center_eq_bot (by simp)] at hgz
      have hxg : g x = 1 := mem_bot.mp hgz
      have he : QuotientGroup.mk' (pCore 2 D) x = 1 := e.injective (hxg.trans e.map_one.symm)
      exact (QuotientGroup.eq_one_iff x).mp he
    have hxU : x ∈ blockU D := hUD.symm ▸ hxcore
    have hfx : (⟨x,hxU⟩ : blockU D) ∈ blockFixed D := hx
    have he : (⟨x,hxU⟩ : blockU D) = 1 := mem_bot.mp (hfixed ▸ hfx)
    exact congrArg Subtype.val he
  have hcard : Nat.card D = 960 := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D),h16,Nat.card_congr e.toEquiv,
      nat_card_alternatingGroup]
    norm_num
  refine ⟨hE,h16,hUD,hfixed,hcenter,hcard,hU,le_antisymm hfc ?_⟩
  intro b hb
  apply MonoidHom.mem_ker.mpr
  have hzD : f b ∈ center D := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a,rfl⟩ := hf y
    simpa only [map_mul] using congrArg f (mem_center_iff.mp hb a)
  simpa only [hcenter,mem_bot] using hzD


variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- In either surviving Mathieu carrier, the literal image of an escaping
natural local member is centerless of order 960, with its whole two-core equal
to its elementary commutator layer of order sixteen. The kernel removed from
the original member is exactly its center, and the original moving four-group
survives injectively in this same carrier quotient. -/
theorem PreExclusionSource.localFamily_linearTwo_mathieu_image
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    let q := QuotientGroup.mk' (center d.L)
    let B := K.subgroupOf d.L
    let D := B.map q
    let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
    IsElementaryAbelian 2 (pCore 2 D) ∧ Nat.card (pCore 2 D) = 16 ∧
      blockU D = pCore 2 D ∧ blockFixed D = ⊥ ∧ center D = ⊥ ∧
      Nat.card D = 960 ∧ (blockU B).map (q.subgroupMap B) = blockU D ∧
      (q.subgroupMap B).ker = center B ∧
      Function.Injective (q.subgroupMap (W.subgroupOf d.L)) ∧
      Nat.card ((W.subgroupOf d.L).map q) = 4 := by
  let q := QuotientGroup.mk' (center d.L)
  let B := K.subgroupOf d.L
  let W := ⁅V,(pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  obtain ⟨_,hn,hWU,hWcard⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  obtain ⟨hKL,_,_,_,_⟩ := s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)
  have hB : IsL2EvenBlock B 2 := (hn ▸ hb : IsL2EvenBlock K 2).of_mulEquiv
    (subgroupOfEquivOfLe hKL.le).symm
  have hqp : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact (d.ordinary_center hL s.odd_core).2
  obtain ⟨name,hname,model⟩ := s.localFamily_linearTwo_carrier_mathieu (h := h)
    hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hm : Nonempty ((d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M22) ∨
      Nonempty ((d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M23) := by
    rcases hname with rfl | rfl
    · exact .inl model
    · exact .inr model
  obtain ⟨hE,h16,hU,hfix,hz,hcard,hUmap,hker⟩ :=
    natural_mathieu_image q hqp (by rw [QuotientGroup.ker_mk']) B hB hm
  obtain ⟨hsplit,hdis,hfixed,_⟩ := s.localFamily_linearTwo_full_action (h := h)
    hG hM hJ hu hfull hK hq hout hb (by omega)
  have hWL : W ≤ d.L := hWU.trans ((map_subtype_le _).trans hKL.le)
  have hinj : Function.Injective (q.subgroupMap (W.subgroupOf d.L)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro w hw
    have hwz : (w.val : d.L) ∈ center d.L :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hw))
    have hwK : (w.val.val : G) ∈ centralizer (K : Set G) := by
      intro k hk
      exact congrArg Subtype.val (mem_center_iff.mp hwz (⟨k,hKL.le hk⟩ : d.L))
    have hwV : (w.val.val : G) ∈ V := hsplit.ge (mem_sup_left w.property)
    have hwF : (w.val.val : G) ∈ V ⊓ centralizer
        ((pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype : Set G) :=
      hfixed.symm ▸ ⟨hwV,hwK⟩
    exact Subtype.ext (Subtype.ext (mem_bot.mp (hdis.le_bot ⟨w.property,hwF⟩)))
  have hwcard : Nat.card ((W.subgroupOf d.L).map q) = 4 := by
    rw [←Nat.card_congr (Equiv.ofBijective _ ⟨hinj,q.subgroupMap_surjective _⟩)]
    exact (Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv).trans hWcard
  exact ⟨hE,h16,hU,hfix,hz,hcard,hUmap,hker,hinj,hwcard⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies the full Mathieu image and the injective
image of its same moving plane. This retains both original source primes,
the literal central-cover map, and the earlier residual input. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_mathieu_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          let q := QuotientGroup.mk' (center d.L)
          let B := K.subgroupOf d.L
          let D := B.map q
          IsElementaryAbelian 2 (pCore 2 D) ∧ Nat.card (pCore 2 D) = 16 ∧
            blockU D = pCore 2 D ∧ blockFixed D = ⊥ ∧ center D = ⊥ ∧
            Nat.card D = 960 ∧ (blockU B).map (q.subgroupMap B) = blockU D ∧
            (q.subgroupMap B).ker = center B ∧
            Function.Injective (q.subgroupMap (m.movingPlane.subgroupOf d.L)) ∧
            Nat.card ((m.movingPlane.subgroupOf d.L).map q) = 4 := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  have hs := s.localFamily_linearTwo_mathieu_image (h := h)
    hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  have hG1 : d.G1 = centralizer (m.Z1 : Set G) := by
    change centralizer (d.Z1 : Set G) = _
    rw [hZ]
  dsimp only at hs
  rw [hG1] at hs
  exact hs

end CFSG.Quasithin.Chapter15.Section01

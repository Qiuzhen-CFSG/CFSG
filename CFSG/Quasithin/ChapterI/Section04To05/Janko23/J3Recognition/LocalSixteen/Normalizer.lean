module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.Coordinates
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
public import Theory.GroupTheory.CentralPrimeQuotientJoin
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.SourceActionSplitting

/-!
# The two source cores induce the full action on E

Both extraspecial cores normalize E because it contains their centers. Each
core has an action image of order two, with kernel the corresponding literal
intersection of order sixteen. The images differ: the first fixes z and the
second fixes u, and fixing both generators of E forces the identity. The join
therefore induces all six automorphisms of the four-group.

The source core-action calculations are adapted from the J₂ `SourceFrame`
implementation, using the H-type reciprocity proved in `ReturningPair`.
Source: Aschbacher, *Sporadic Groups* (1994), 8.15(1,5), 46.2–46.3,
printed pp.29–30 and 251. All actions below are restrictions of the literal
normalizer conjugation map.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Normalizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

theorem E_kleinFour : IsKleinFour P.E := by
  let : IsElementaryAbelian 2 P.E := P.E_elementary
  let : Nontrivial P.E := Finite.one_lt_card_iff_nontrivial.mp (by rw [P.E_card]; decide)
  exact ⟨P.E_card, IsElementaryAbelian.exponent_eq_prime⟩

omit [Finite G] in
private theorem extraspecial_normalizes {Q E : Subgroup G} [IsExtraspecial 2 Q]
    (hE : E ≤ Q) (hZ : (center Q).map Q.subtype ≤ E) :
    Q ≤ normalizer (E : Set G) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  intro q hq r hr
  have hc : ⁅(⟨q, hq⟩ : Q), (⟨r, hE hr⟩ : Q)⁆ ∈ center Q :=
    (IsExtraspecial.quotient_elementary_abelian 2 Q).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top _) (mem_top _))
  exact hZ (mem_map_of_mem Q.subtype hc)

theorem core_le_normalizer_E : ambientCore D.z ≤ normalizer (P.E : Set G) := by
  let := D.localType.ambientCore_isExtraspecial
  apply extraspecial_normalizes P.E_le_core
  rw [D.localType.core_center_image]
  exact le_sup_left

theorem conjugateCore_extraspecial : IsExtraspecial 2 P.conjugateCore :=
  IsExtraspecial.of_mulEquiv
    ((ambientCore D.z).equivMapOfInjective (MulAut.conj P.g).toMonoidHom
      (MulAut.conj P.g).injective) D.localType.ambientCore_isExtraspecial

theorem conjugateCore_center_image :
    (center P.conjugateCore).map P.conjugateCore.subtype = zpowers P.u := by
  let := conjugateCore_extraspecial P
  apply (eq_of_le_of_card_ge ?_ ?_).symm
  · apply zpowers_le.mpr
    refine mem_map.mpr ⟨⟨P.u, P.u_mem_conjugateCore⟩, mem_center_iff.mpr ?_, rfl⟩
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (P.conjugateCore_le x.property))
  · rw [card_map_of_injective P.conjugateCore.subtype_injective,
      IsExtraspecial.center_order_p (p := 2), Nat.card_zpowers, P.u_order]

theorem conjugateCore_le_normalizer_E :
    P.conjugateCore ≤ normalizer (P.E : Set G) := by
  let := conjugateCore_extraspecial P
  apply extraspecial_normalizes (P.E_le_conjugateCore )
  rw [conjugateCore_center_image P]
  exact le_sup_right

def coreJoin : Subgroup G := ambientCore D.z ⊔ P.conjugateCore

theorem coreJoin_le_normalizer_E :
    coreJoin P ≤ normalizer (P.E : Set G) :=
  sup_le (core_le_normalizer_E P) (conjugateCore_le_normalizer_E P)

def coreJoinAction : coreJoin P →* MulAut P.E :=
  P.E.normalizerMonoidHom.comp (inclusion (coreJoin_le_normalizer_E P))

private def restrictedAction (E K : Subgroup G) (h : K ≤ normalizer (E : Set G)) :
    K →* MulAut E := E.normalizerMonoidHom.comp (inclusion h)

omit [Finite G] in
private theorem restrictedAction_ker (E K : Subgroup G) (h : K ≤ normalizer (E : Set G)) :
    (restrictedAction E K h).ker = (centralizer (E : Set G)).subgroupOf K := by
  rw [restrictedAction, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

theorem core_inf_centralizer_E : ambientCore D.z ⊓ centralizer (P.E : Set G) = P.leftCore := by
  rw [ReturningPair.centralizer_E_eq, ← inf_assoc, inf_eq_left.mpr (ambientCore_le D.z)]
  rfl

theorem conjugateCore_inf_centralizer_E :
    P.conjugateCore ⊓ centralizer (P.E : Set G) = P.rightCore := by
  rw [ReturningPair.centralizer_E_eq, inf_comm (involutionCentralizer D.z), ← inf_assoc,
    inf_eq_left.mpr P.conjugateCore_le]
  rfl

private theorem restrictedAction_range_card (K : Subgroup G)
    (hK : K ≤ normalizer (P.E : Set G))
    (hk : Nat.card K = 32) (hc : Nat.card (K ⊓ centralizer (P.E : Set G) : Subgroup G) = 16) :
    Nat.card (restrictedAction P.E K hK).range = 2 := by
  have hker : Nat.card (restrictedAction P.E K hK).ker = 16 := by
    rw [restrictedAction_ker]
    rw [← inf_subgroupOf_right (centralizer (P.E : Set G)) K]
    rw [Nat.card_congr (subgroupOfEquivOfLe (show centralizer (P.E : Set G) ⊓ K ≤ K from inf_le_right)).toEquiv]
    rwa [inf_comm]
  have hh := (restrictedAction P.E K hK).ker.card_mul_index
  rw [hker, index_ker, hk] at hh
  omega

private theorem E_aut_ext (a b : MulAut P.E)
    (hz : a ⟨D.z, P.z_mem_E⟩ = b ⟨D.z, P.z_mem_E⟩)
    (hu : a ⟨P.u, P.u_mem_E⟩ = b ⟨P.u, P.u_mem_E⟩) : a = b := by
  let K := a.toMonoidHom.eqLocus b.toMonoidHom
  have h : P.E ≤ K.map P.E.subtype :=
    sup_le (zpowers_le.mpr ⟨⟨D.z, P.z_mem_E⟩, hz, rfl⟩)
      (zpowers_le.mpr ⟨⟨P.u, P.u_mem_E⟩, hu, rfl⟩)
  apply MulEquiv.ext
  intro x
  obtain ⟨y, hy, he⟩ := h x.property
  have hyx : y = x := Subtype.ext he
  subst y
  exact hy

theorem coreJoinAction_surjective :
    Function.Surjective (coreJoinAction P) := by
  let : IsKleinFour P.E := E_kleinFour P
  let f := coreJoinAction P
  let a := restrictedAction P.E (ambientCore D.z) (core_le_normalizer_E P)
  let b := restrictedAction P.E P.conjugateCore (conjugateCore_le_normalizer_E P)
  have ha : Nat.card a.range = 2 := restrictedAction_range_card P _ _
    D.localType.ambientCore_card (by rw [core_inf_centralizer_E, P.leftCore_card])
  have hqb : Nat.card P.conjugateCore = 32 := by
    rw [ReturningPair.conjugateCore, card_map_of_injective (MulAut.conj P.g).injective]
    exact D.localType.ambientCore_card
  have hb : Nat.card b.range = 2 := restrictedAction_range_card P _ _ hqb
    (by rw [conjugateCore_inf_centralizer_E, P.rightCore_card ])
  have ha_le : a.range ≤ f.range := by
    rintro x ⟨q, rfl⟩
    exact ⟨⟨q, (le_sup_left : ambientCore D.z ≤ coreJoin P) q.property⟩, rfl⟩
  have hb_le : b.range ≤ f.range := by
    rintro x ⟨q, rfl⟩
    exact ⟨⟨q, (le_sup_right : P.conjugateCore ≤ coreJoin P) q.property⟩, rfl⟩
  have hne : a.range ≠ b.range := by
    intro he
    have hbot : a.range = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      apply mem_bot.mpr
      apply E_aut_ext P x 1
      · obtain ⟨q, rfl⟩ := hx
        apply Subtype.ext
        change (q : G) * D.z * (q : G)⁻¹ = D.z
        exact mul_inv_eq_iff_eq_mul.mpr
          (mem_centralizer_singleton_iff.mp (ambientCore_le D.z q.property))
      · obtain ⟨q, hq⟩ := he ▸ hx
        rw [← hq]
        apply Subtype.ext
        change (q : G) * P.u * (q : G)⁻¹ = P.u
        exact mul_inv_eq_iff_eq_mul.mpr
          (mem_centralizer_singleton_iff.mp (P.conjugateCore_le q.property))
    rw [hbot, card_bot] at ha
    omega
  have hd : Nat.card f.range ∣ 6 := by
    simpa only [IsKleinFour.card_mulAut] using card_subgroup_dvd_card f.range
  have hd2 : 2 ∣ Nat.card f.range := ha ▸ card_dvd_of_le ha_le
  have hc : Nat.card f.range = 2 ∨ Nat.card f.range = 6 := by
    have hu := Nat.le_of_dvd (by decide : 0 < 6) hd
    interval_cases hn : Nat.card f.range <;>
      (try norm_num [hn] at hd) <;> (try norm_num [hn] at hd2) <;> simp_all
  have hc6 : Nat.card f.range = 6 := hc.resolve_left (fun h => hne
    ((eq_of_le_of_card_ge ha_le (by omega)).trans
      (eq_of_le_of_card_ge hb_le (by omega)).symm))
  apply MonoidHom.range_eq_top.mp
  exact eq_top_of_card_eq f.range (hc6.trans (IsKleinFour.card_mulAut P.E).symm)
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Normalizer

/-!
# The full root normalizer under H-type alone

The local core orbit gives |C_G(E)| = 192. Its characteristic Sylow
subgroup R has order 64, so N_G(E) = N_G(R). The two cores induce distinct
involutions in Aut(E), giving its full order-six action and |N_G(R)| = 1152.

Write C = C_G(E). Relative normality gives [Q,C] ≤ Q ∩ C ≤ R and the
corresponding bound for the conjugate core. The full action yields
N_G(E) = ⟨Q,Q^g,C⟩. Since C/R has order three, its image is central in
N_G(R)/R. A nonidentity image gives the required central cubic coset.
The intrinsic-center action is transported through the actual equality
E = Z(R), and the generic `RootNormalizerModel.SourceAction` theorems identify and
split the actual normalizer, preserving its embedded root subgroup.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15(5), 46.2–46.3 and
46.14, printed pp.29–30, 251, 257–258. The V of 8.15 is our marked E.
No normalizer complement, ambient group order, or second centralizer is used.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Normalizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

theorem normalizer_E_action_surjective :
    Function.Surjective P.E.normalizerMonoidHom := by
  intro b
  obtain ⟨x, hx⟩ := coreJoinAction_surjective P b
  exact ⟨inclusion (coreJoin_le_normalizer_E P) x, hx⟩

theorem normalizer_E_card :
    Nat.card (normalizer (P.E : Set G)) = 1152 := by
  let : IsKleinFour P.E := E_kleinFour P
  have hker : Nat.card P.E.normalizerMonoidHom.ker = 192 := by
    rw [normalizerMonoidHom_ker]
    exact (Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (P.E : Set G))).toEquiv).trans
      (P.centralizer_E_card)
  have hrange := MonoidHom.range_eq_top.mpr (normalizer_E_action_surjective P)
  have hh := P.E.normalizerMonoidHom.ker.card_mul_index
  rw [hker, index_ker, hrange, card_top, IsKleinFour.card_mulAut] at hh
  exact hh.symm

theorem normalizer_R_card :
    Nat.card (normalizer (P.R : Set G)) = 1152 := by
  rw [← Coordinates.normalizer_E_eq_normalizer_R P ]
  exact normalizer_E_card P

noncomputable def centerEquivE : center P.R ≃* P.E :=
  ((center P.R).equivMapOfInjective P.R.subtype P.R.subtype_injective).trans
    (MulEquiv.subgroupCongr (E_center P))

theorem full_center_action :
    ∀ b : MulAut (center P.R), ∃ n : normalizer (P.R : Set G),
      ∀ z : center P.R, P.R.normalizerMonoidHom n z = (b z : P.R) := by
  intro b
  let e := centerEquivE P
  obtain ⟨n, hn⟩ := normalizer_E_action_surjective P (MulAut.congr e b)
  refine ⟨⟨n, (Coordinates.normalizer_E_eq_normalizer_R P) ▸ n.property⟩, ?_⟩
  intro z
  apply Subtype.ext
  have hz := congrArg (fun t : P.E => (t : G)) (MulEquiv.congr_fun hn (e z))
  change (n : G) * ((z : P.R) : G) * (n : G)⁻¹ = ((b (e.symm (e z)) : P.R) : G) at hz
  rw [e.symm_apply_apply] at hz
  exact hz

theorem normalizer_E_eq_coreJoin_sup_centralizer :
    normalizer (P.E : Set G) = coreJoin P ⊔ centralizer (P.E : Set G) := by
  apply le_antisymm
  · intro n hn
    obtain ⟨x, hx⟩ := coreJoinAction_surjective P (P.E.normalizerMonoidHom ⟨n, hn⟩)
    let xN := inclusion (coreJoin_le_normalizer_E P) x
    have he : P.E.normalizerMonoidHom xN = P.E.normalizerMonoidHom ⟨n, hn⟩ := hx
    have hk : xN⁻¹ * ⟨n, hn⟩ ∈ P.E.normalizerMonoidHom.ker := by
      change P.E.normalizerMonoidHom (xN⁻¹ * ⟨n, hn⟩) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    rw [normalizerMonoidHom_ker] at hk
    change (x : G)⁻¹ * n ∈ centralizer (P.E : Set G) at hk
    have hh := (coreJoin P ⊔ centralizer (P.E : Set G)).mul_mem
      (mem_sup_left x.property) (mem_sup_right hk)
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le (coreJoin_le_normalizer_E P) (Subgroup.centralizer_le_normalizer _)

theorem core_commutator_centralizer_le_R :
    ⁅ambientCore D.z, centralizer (P.E : Set G)⁆ ≤ P.R := by
  apply le_trans _ (show P.leftCore ≤ P.R from le_sup_left)
  rw [← core_inf_centralizer_E P]
  apply le_inf
  · apply le_normalizer_iff_commutator_le_left.mp
    rw [D.localType.normalizer_core, ReturningPair.centralizer_E_eq]
    exact inf_le_left
  · apply le_normalizer_iff_commutator_le_right.mp
    exact (core_le_normalizer_E P).trans (normalizer_le_normalizer_centralizer P.E)

theorem conjugateCore_commutator_centralizer_le_R :
    ⁅P.conjugateCore, centralizer (P.E : Set G)⁆ ≤ P.R := by
  apply le_trans _ (show P.rightCore ≤ P.R from le_sup_right)
  rw [← conjugateCore_inf_centralizer_E P]
  apply le_inf
  · apply le_normalizer_iff_commutator_le_left.mp
    rw [P.normalizer_conjugateCore, ReturningPair.centralizer_E_eq]
    exact inf_le_right
  · apply le_normalizer_iff_commutator_le_right.mp
    exact (conjugateCore_le_normalizer_E P).trans (normalizer_le_normalizer_centralizer P.E)

/-- A nonidentity central cubic coset in the literal normalizer quotient. -/
theorem central_cubic :
    ∃ c : normalizer (P.R : Set G), (c : G) ∉ P.R ∧ (c : G) ^ 3 ∈ P.R ∧
      ∀ n : normalizer (P.R : Set G), ⁅(c : G), (n : G)⁆ ∈ P.R := by
  let N := normalizer (P.R : Set G)
  let C := centralizer (P.E : Set G)
  let T := P.R.subgroupOf N
  let A := (ambientCore D.z).subgroupOf N
  let B := P.conjugateCore.subgroupOf N
  let C' := C.subgroupOf N
  let π := QuotientGroup.mk' T
  have hQN : ambientCore D.z ≤ N :=
    (core_le_normalizer_E P).trans (Coordinates.normalizer_E_eq_normalizer_R P).le
  have hBN : P.conjugateCore ≤ N :=
    (conjugateCore_le_normalizer_E P).trans (Coordinates.normalizer_E_eq_normalizer_R P).le
  have hCN : C ≤ N := centralizer_E_le_normalizer_R P
  have hgen : A ⊔ B ⊔ C' = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le hQN, map_subgroupOf_eq_of_le hBN,
      map_subgroupOf_eq_of_le hCN, ← MonoidHom.range_eq_map, N.range_subtype]
    exact (normalizer_E_eq_coreJoin_sup_centralizer P).symm.trans
      (Coordinates.normalizer_E_eq_normalizer_R P)
  have hc : Nat.card (C'.map π) = 3 := by
    rw [← relIndex_ker, QuotientGroup.ker_mk']
    change (P.R.subgroupOf N).relIndex (C.subgroupOf N) = 3
    rw [relIndex_subgroupOf hCN]
    change (P.R.subgroupOf C).index = 3
    have hr : Nat.card (P.R.subgroupOf C) = 64 :=
      (Nat.card_congr (subgroupOfEquivOfLe (P.R_le_centralizer_E)).toEquiv).trans (P.R_card )
    have hh := (P.R.subgroupOf C).card_mul_index
    rw [hr, P.centralizer_E_card] at hh
    omega
  have ha : ⁅A, C'⁆ ≤ π.ker := by
    rw [QuotientGroup.ker_mk']
    apply commutator_le.mpr
    intro a ha c hc
    exact core_commutator_centralizer_le_R P
      (commutator_mem_commutator (show (a : G) ∈ ambientCore D.z from ha)
        (show (c : G) ∈ C from hc))
  have hb : ⁅B, C'⁆ ≤ π.ker := by
    rw [QuotientGroup.ker_mk']
    apply commutator_le.mpr
    intro b hb c hc
    exact conjugateCore_commutator_centralizer_le_R P
      (commutator_mem_commutator (show (b : G) ∈ P.conjugateCore from hb)
        (show (c : G) ∈ C from hc))
  obtain ⟨c, _, hcout, hc3, hcomm⟩ :=
    exists_central_prime_coset_of_generators π A B C' hgen hc ha hb
  rw [QuotientGroup.ker_mk'] at hcout hc3 hcomm
  exact ⟨c, hcout, hc3, hcomm⟩

end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Normalizer

namespace CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Normalizer
open Matrix.PSL3Four
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

/-- The full original root normalizer, with its literal embedded root preserved.
The action and splitting theorems are applied to the relative normal subgroup. -/
theorem exists_identification :
    ∃ (d : P.R ≃* RootNormalizerModel.Root)
      (f : normalizer (P.R : Set G) ≃* RootNormalizerModel.Model),
      ∀ r : P.R, f (inclusion le_normalizer r) = SemidirectProduct.inl (d r) := by
  let N := normalizer (P.R : Set G)
  let Q := P.R.subgroupOf N
  let eQR : Q ≃* P.R := subgroupOfEquivOfLe le_normalizer
  obtain ⟨e⟩ := Coordinates.rootEquiv P
  have hc : centralizer (Q : Set N) ≤ Q := by
    intro n hn
    apply selfCentralizing P
    intro r hr
    exact congrArg Subtype.val (hn (⟨r, le_normalizer hr⟩ : N) hr)
  have hZ : ∀ b : MulAut (center Q), ∃ n : N,
      ∀ z : center Q, MulAut.conjNormal n z = (b z : Q) := by
    intro b
    let ec : center Q ≃* center P.R := centerCongr eQR
    obtain ⟨n, hn⟩ := full_center_action P (MulAut.congr ec b)
    refine ⟨n, ?_⟩
    intro z
    apply eQR.injective
    have hz := hn (ec z)
    change P.R.normalizerMonoidHom n (eQR z) = eQR (b (ec.symm (ec z))) at hz
    rw [ec.symm_apply_apply] at hz
    exact hz
  have hthree : ∃ c : N, c ∉ Q ∧ c ^ 3 ∈ Q ∧ ∀ n : N, ⁅c,n⁆ ∈ Q := by
    obtain ⟨c,hc,hc3,hcn⟩ := central_cubic P
    exact ⟨c,hc,hc3,hcn⟩
  obtain ⟨d,hd⟩ := RootNormalizerModel.SourceAction.exists_adjusted_coordinates Q
    (eQR.trans e) hc (normalizer_R_card P) hZ hthree
  obtain ⟨f,hf⟩ := RootNormalizerModel.SourceAction.exists_model_equiv Q d hc hd
  refine ⟨eQR.symm.trans d,f,?_⟩
  intro r
  exact hf (eQR.symm r)
end CFSG.Quasithin.Janko23.J3Recognition.LocalSixteen.Geometry.Normalizer

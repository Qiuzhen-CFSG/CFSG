module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.Contracts
public import Glauberman.ZStar
public import Theory.GroupTheory.InvolutionCentralizerLifting
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Z-star in the literal Suzuki point-stabilizer quotient

Write A for the distinguished closure in M and Q for N_M(AU). The
intersection of A and U is trivial, so U retains order two in M/A. Its
specified Sylow overgroup and weak closure descend along the actual quotient
map. Glauberman's Z-star theorem and coprime centralizer lifting then give
M/A = O₂′(M/A) Q̄.

The remaining results take the local calculation O₂′(Q̄) = 1 explicitly.
It makes the odd-core intersection trivial; the nonidentity element of Ū
acts without nonidentity fixed points, hence by inversion. The odd core is
therefore abelian. If p is absent from |Q̄|, its p-core is a Sylow subgroup.
The local normalizer calculation and the invariant lift to M are separate
obligations; this module does not assert Proposition 14.1.

Source: GLS, Volume 4, Chapter 2, final paragraph of Proposition 14.1,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2620–2630. Here `pPrimeCore 2`
is O₂′, not either of the two residuals.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory PFAppendixIII
open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

namespace ZStarDescent

/-- The source normalizer Q, as a subgroup of M. -/
@[expose] public def normalizerAU (g : LocalGeometry Z M z t m) : Subgroup M :=
  (normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G)).subgroupOf M

public theorem U_le_M (g : LocalGeometry Z M z t m) : g.U ≤ M := by
  rw [g.U_eq]
  exact inf_le_left.trans (g.T_lt_S.le.trans g.S_le_M)

public theorem A_disjoint_U (g : LocalGeometry Z M z t m) :
    Disjoint (closure (Z ∩ (M : Set G))) g.U := by
  have hAP : closure (Z ∩ (M : Set G)) ≤ borelTwoCore M z t := by
    rw [← g.P_center]
    exact map_subtype_le _
  exact g.P_disjoint_U.mono_left hAP

/-- U embeds into the literal quotient M/A, hence retains order two. -/
public theorem quotient_U_card (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (hU : Nat.card g.U = 2) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    Nat.card ((g.U.subgroupOf M).map (QuotientGroup.mk' A)) = 2 := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' A
  have hinj : Set.InjOn pi (g.U.subgroupOf M) := by
    apply (Set.injOn_iff_map_eq_one pi (g.U.subgroupOf M)).mpr
    intro x hx hpi
    have hxA : (x : G) ∈ closure (Z ∩ (M : Set G)) :=
      (QuotientGroup.eq_one_iff (N := A) x).mp hpi
    apply Subtype.ext
    exact (disjoint_iff_inf_le.mp (A_disjoint_U g)) ⟨hxA, hx⟩
  calc
    Nat.card ((g.U.subgroupOf M).map pi) = Nat.card (g.U.subgroupOf M) :=
      Nat.card_image_of_injOn hinj
    _ = Nat.card g.U := Nat.card_congr (subgroupOfEquivOfLe (U_le_M g)).toEquiv
    _ = 2 := hU

/-- The specified ambient Sylow subgroup descends under the actual quotient map. -/
public theorem quotient_S_sylow (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    ∃ V : Sylow 2 (M ⧸ A),
      (V : Subgroup (M ⧸ A)) = (g.S.subgroupOf M).map (QuotientGroup.mk' A) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hV⟩ := s.S_sylow
  let W := V.subtype (hV ▸ g.S_le_M)
  refine ⟨W.mapSurjective (QuotientGroup.mk'_surjective A), ?_⟩
  rw [Sylow.coe_mapSurjective]
  change ((V : Subgroup G).subgroupOf M).map _ = _
  rw [hV]

/-- Z-star applied in M/A, with no assumption about the odd core. -/
public theorem quotient_U_le_center_mod_oddCore (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (hweak : QuotientFusion d g) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' A
    ((g.U.subgroupOf M).map pi).map (QuotientGroup.mk' (pPrimeCore 2 (M ⧸ A))) ≤
      center ((M ⧸ A) ⧸ pPrimeCore 2 (M ⧸ A)) := by
  obtain ⟨V, hV⟩ := quotient_S_sylow d g s
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  apply Glauberman.weaklyClosedInvolution_le_center_quotient_oddCore V _
    (quotient_U_card d g hU)
  rw [hV]
  exact hweak

/-- The normalizer in the quotient is precisely the image of N_M(AU). -/
public theorem normalizerAU_image (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' A
    (normalizerAU g).map pi = normalizer (((g.U.subgroupOf M).map pi) : Set (M ⧸ A)) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' A
  have hpre : (((g.U.subgroupOf M).map pi).comap pi) =
      (closure (Z ∩ (M : Set G)) ⊔ g.U).subgroupOf M := by
    rw [comap_map_eq, QuotientGroup.ker_mk',
      subgroupOf_sup distinguishedClosure_le (U_le_M g)]
    exact sup_comm _ _
  have he : (normalizer (((g.U.subgroupOf M).map pi) : Set (M ⧸ A))).comap pi =
      normalizerAU g := by
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective A), hpre,
      ← subgroupOf_normalizer_eq (sup_le distinguishedClosure_le (U_le_M g))]
    rfl
  change (normalizerAU g).map pi = normalizer ((g.U.subgroupOf M).map pi : Set (M ⧸ A))
  rw [← he, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective A)]

/-- Z-star and coprime centralizer lifting give the source odd-core supplement. -/
public theorem oddCore_sup_normalizerAU_image (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) (hweak : QuotientFusion d g) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' A
    pPrimeCore 2 (M ⧸ A) ⊔ (normalizerAU g).map pi = ⊤ := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' A
  let B := (g.U.subgroupOf M).map pi
  have hc : Nat.card B = 2 := quotient_U_card d g hU
  have hne : B ≠ ⊥ := (one_lt_card_iff_ne_bot B).mp (by omega)
  obtain ⟨u, hu, hu1⟩ := B.bot_or_exists_ne_one.resolve_left hne
  have huI : PFAppendixIII.IsInvolution u := by
    have ho : orderOf u = 2 := by
      have hd := B.orderOf_dvd_natCard hu
      rw [hc] at hd
      exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
        (fun h => hu1 (orderOf_eq_one_iff.mp h))
    exact ⟨hu1, by rw [← ho]; exact pow_orderOf_eq_one u⟩
  have hB : zpowers u = B := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hu)
    rw [Nat.card_zpowers, orderOf_eq_prime huI.sq_eq_one huI.ne_one, hc]
  have hcenter := quotient_U_le_center_mod_oddCore d g s hU hweak
  have hsup := oddCore_sup_involution_centralizer huI
    (hcenter (mem_map_of_mem _ hu))
  apply top_unique
  rw [← hsup]
  apply sup_le_sup_left
  rw [normalizerAU_image d g]
  have he : centralizer ({u} : Set (M ⧸ A)) = centralizer (B : Set (M ⧸ A)) := by
    rw [← hB, zpowers_eq_closure, centralizer_closure]
  rw [he]
  exact Subgroup.centralizer_le_normalizer _

/-- Trivial odd core in the source normalizer implies its image has trivial
intersection with the ambient odd core. Normality is only required for the
ambient odd core and is restricted to the image subgroup. -/
public theorem oddCore_disjoint_of_normalizer_oddCore_eq_bot
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    let Qbar := (normalizerAU g).map (QuotientGroup.mk' A)
    pPrimeCore 2 Qbar = ⊥ → Disjoint (pPrimeCore 2 (M ⧸ A)) Qbar := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  let Qbar := (normalizerAU g).map (QuotientGroup.mk' A)
  let O := pPrimeCore 2 (M ⧸ A)
  change pPrimeCore 2 Qbar = ⊥ → Disjoint O Qbar
  intro hcore
  have hcop : Nat.Coprime 2 (Nat.card (O.subgroupOf Qbar)) := by
    rw [← card_map_of_injective (K := O.subgroupOf Qbar) Qbar.subtype_injective,
      subgroupOf_map_subtype]
    exact Nat.Coprime.of_dvd_right (card_dvd_of_le inf_le_left) pPrimeCore_coprime_card
  have hle : O.subgroupOf Qbar ≤ pPrimeCore 2 Qbar :=
    le_sSup ⟨inferInstance, hcop⟩
  apply disjoint_iff_inf_le.mpr
  intro x hx
  have hh := hle (show (⟨x, hx.2⟩ : Qbar) ∈ O.subgroupOf Qbar from hx.1)
  rw [hcore] at hh
  exact congrArg Subtype.val (mem_bot.mp hh)

/-- Each nonidentity element of the image of U inverts the odd core once
its intersection with the normalizer image is trivial. -/
public theorem oddCore_inverted_of_disjoint
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hU : Nat.card g.U = 2) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' A
    let O := pPrimeCore 2 (M ⧸ A)
    Disjoint O ((normalizerAU g).map pi) →
      ∀ u ∈ (g.U.subgroupOf M).map pi, u ≠ 1 →
        ∀ x ∈ O, u * x * u⁻¹ = x⁻¹ := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' A
  let O := pPrimeCore 2 (M ⧸ A)
  let B := (g.U.subgroupOf M).map pi
  change Disjoint O ((normalizerAU g).map pi) →
    ∀ u ∈ B, u ≠ 1 → ∀ x ∈ O, u * x * u⁻¹ = x⁻¹
  intro hdisj u hu hu1
  have hc : Nat.card B = 2 := quotient_U_card d g hU
  have ho : orderOf u = 2 := by
    have hd := B.orderOf_dvd_natCard hu
    rw [hc] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun h => hu1 (orderOf_eq_one_iff.mp h))
  have hu2 : u ^ 2 = 1 := by rw [← ho]; exact pow_orderOf_eq_one u
  have hB : zpowers u = B := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hu)
    rw [Nat.card_zpowers, ho, hc]
  have hC : centralizer ({u} : Set (M ⧸ A)) ≤ (normalizerAU g).map pi := by
    rw [normalizerAU_image d g]
    change centralizer {u} ≤ normalizer (B : Set (M ⧸ A))
    rw [← hB, zpowers_eq_closure]
    exact (centralizer_closure {u}).symm ▸ Subgroup.centralizer_le_normalizer _
  let phi : MulAut O := MulAut.conjNormal u
  have hfree : MonoidHom.FixedPointFree phi := by
    intro x hx
    have hxC : (x : M ⧸ A) ∈ centralizer ({u} : Set (M ⧸ A)) := by
      apply mem_centralizer_singleton_iff.mpr
      exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hx)).symm
    apply Subtype.ext
    exact disjoint_iff_inf_le.mp hdisj ⟨x.property, hC hxC⟩
  have hinvol : Function.Involutive phi := by
    intro x
    let psi : M ⧸ A →* MulAut O := MulAut.conjNormal
    change (psi u * psi u) x = x
    rw [← map_mul, ← pow_two, hu2, map_one]
    rfl
  intro x hx
  exact congrArg Subtype.val
    (congrFun (hfree.coe_eq_inv_of_involutive hinvol) ⟨x, hx⟩)

/-- The odd core of M/A is abelian under the outstanding local odd-core
premise for the source normalizer. -/
public theorem oddCore_abelian_of_normalizer_oddCore_eq_bot
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hU : Nat.card g.U = 2) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    let pi := QuotientGroup.mk' A
    pPrimeCore 2 ((normalizerAU g).map pi) = ⊥ →
      IsMulCommutative (pPrimeCore 2 (M ⧸ A)) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  let pi := QuotientGroup.mk' A
  let O := pPrimeCore 2 (M ⧸ A)
  let B := (g.U.subgroupOf M).map pi
  change pPrimeCore 2 ((normalizerAU g).map pi) = ⊥ → IsMulCommutative O
  intro hcore
  have hc : Nat.card B = 2 := quotient_U_card d g hU
  have hne : B ≠ ⊥ := (one_lt_card_iff_ne_bot B).mp (by omega)
  obtain ⟨u, hu, hu1⟩ := B.bot_or_exists_ne_one.resolve_left hne
  have hinv := oddCore_inverted_of_disjoint d g hU
    (oddCore_disjoint_of_normalizer_oddCore_eq_bot d g hcore) u hu hu1
  have hi (x : O) : MulAut.conjNormal u x = x⁻¹ :=
    Subtype.ext (hinv x x.property)
  refine ⟨⟨fun x y => ?_⟩⟩
  have hh := map_mul (MulAut.conjNormal u : MulAut O) x⁻¹ y⁻¹
  simpa only [hi, mul_inv_rev, inv_inv] using hh.symm

/-- After the local normalizer calculation, the p-core in M/A is a Sylow
p-subgroup. This still requires lifting a Sylow subgroup to M. -/
public theorem quotient_pCore_sylow_of_normalizer
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) (hweak : QuotientFusion d g)
    (p : ℕ) [Fact p.Prime] :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    let Qbar := (normalizerAU g).map (QuotientGroup.mk' A)
    pPrimeCore 2 Qbar = ⊥ → ¬ p ∣ Nat.card Qbar →
      ∃ R : Sylow p (M ⧸ A), (R : Subgroup (M ⧸ A)) = pCore p (M ⧸ A) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  let X := M ⧸ A
  let O := pPrimeCore 2 X
  let Qbar := (normalizerAU g).map (QuotientGroup.mk' A)
  change pPrimeCore 2 Qbar = ⊥ → ¬ p ∣ Nat.card Qbar →
    ∃ R : Sylow p X, (R : Subgroup X) = pCore p X
  intro hcore hpQ
  have hsup : O ⊔ Qbar = ⊤ := oddCore_sup_normalizerAU_image d g s hU hweak
  have hindex : ¬ p ∣ O.index := by
    have he : O.relIndex Qbar = O.index := by
      rw [← relIndex_sup_left, hsup, relIndex_top_right]
    intro hd
    rw [← he] at hd
    exact hpQ (hd.trans (O.relIndex_dvd_card Qbar))
  let : IsMulCommutative O := oddCore_abelian_of_normalizer_oddCore_eq_bot d g hU hcore
  let : CommGroup O := inferInstance
  let P : Sylow p O := Classical.choice inferInstance
  have hpIndex : ¬ p ∣ ((P : Subgroup O).map O.subtype).index := by
    rw [index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul P.not_dvd_index hindex
  let R := (P.isPGroup'.map O.subtype).toSylow hpIndex
  have hRle : (R : Subgroup X) ≤ pCore p X :=
    P.map_le_pCore inferInstance inferInstance p
  refine ⟨R, ?_⟩
  exact le_antisymm hRle (pCore_isPGroup.le_sylow_of_normal R)

end ZStarDescent
end BenderSuzuki.ZD.SuzukiExclusion

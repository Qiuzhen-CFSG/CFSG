module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.HallAdjustment
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.ElementaryBranch
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.SylowStructure.CommonPrime
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SubgroupProductCard


/-!
# Hall geometry from a normal centralizer Sylow subgroup

For the source subgroups A = M°, J = C_G(L), and R = C_M(A) ∩ N_M(AU),
we prove C_G(AU) = T and N_G(AU) = N_G(T). If U is normal in J, its
Sylow characteristic property makes it normal in D. The source normalizer
product then identifies R with SY for every odd complement J = UY.
This proves solvability and the exact Hall property in R, and shows that
M ∩ N_G(L) preserves AU. The final theorem discharges all the extra
geometric premises of the Hall-conjugator adjustment.

Normality of U in J and the existence of the odd complement remain explicit;
the solvable Suzuki subgroup analysis must supply them when |U| > 2.
Source: GLS4, Chapter 2, Lemmas 14.6–14.8, refs/KGroup/GLS4/Chapter2.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

public theorem Context.centralizer_closure_sup_U (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    centralizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) = g.T := by
  have hUne : g.U ≠ ⊥ := (one_lt_card_iff_ne_bot _).mp (d.two_le_U_card g)
  obtain ⟨u, hu1⟩ := ne_bot_iff_exists_ne_one.mp hUne
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hT := g.centralizer_U u u.property hu1'
  apply le_antisymm
  · rw [← hT]
    exact le_inf (centralizer_le (show (closure (Z ∩ (M : Set G)) : Set G) ⊆
      ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) from fun _ hx => mem_sup_left hx))
        (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_right u.property)))
  · apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp (hT ▸ inf_le_left)
    · intro v hv x hx
      by_cases hv1 : v = 1
      · simp [hv1]
      · have hxc : x ∈ centralizer ({v} : Set G) :=
          ((g.centralizer_U v hv hv1).symm ▸ hx).2
        exact mem_centralizer_singleton_iff.mp hxc

public theorem Context.normalizer_closure_sup_U_eq (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) :
    normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) =
      normalizer (g.T : Set G) := by
  apply le_antisymm
  · rw [← d.centralizer_closure_sup_U g]
    exact normalizer_le_normalizer_centralizer _
  · rw [← g.omega_T_eq]
    let : (omega₁ g.T (p := 2)).Characteristic := omega₁_characteristic _
    exact normalizer_le_normalizer_characteristic_image g.T (omega₁ g.T (p := 2))

public theorem SylowGeometry.S_le_complementFusionGroup (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) : g.S ≤ complementFusionGroup g := by
  have hSA : g.S ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
    intro x hx a ha
    rw [← s.S_center] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    exact (congrArg Subtype.val ((mem_center_iff.mp ha) ⟨x, hx⟩)).symm
  have hST : g.S ≤ normalizer (g.T : Set G) :=
    (normal_subgroupOf_iff_le_normalizer g.T_lt_S.le).mp s.T_normal
  have hSΩ : g.S ≤ normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) := by
    rw [← g.omega_T_eq]
    let : (omega₁ g.T (p := 2)).Characteristic := omega₁_characteristic _
    exact hST.trans (normalizer_le_normalizer_characteristic_image g.T (omega₁ g.T (p := 2)))
  exact le_inf (le_inf g.S_le_M hSA) hSΩ

public theorem Context.pair_normalizes_U_of_normal (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal) :
    residualPairStabilizer M t ≤ normalizer (g.U : Set G) := by
  let J := centralizer (residualGenerated M z t : Set G)
  obtain ⟨V, hV⟩ := g.U_sylow_centralizer
  have he : g.U.subgroupOf J = (V : Subgroup J) := by
    rw [← hV]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hn : (V : Subgroup J).Normal := he ▸ hU
  let : (V : Subgroup J).Characteristic := V.characteristic_of_normal hn
  rw [← hV]
  exact (d.pair_le_residual_normalizer.trans
    (normalizer_le_normalizer_centralizer (residualGenerated M z t))).trans
      (normalizer_le_normalizer_characteristic_image J (V : Subgroup J))

public theorem Context.U_normal_pair_of_normal (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal) :
    (g.U.subgroupOf (residualPairStabilizer M t)).Normal :=
  (normal_subgroupOf_iff_le_normalizer
    (g.U_le_centralizer.trans d.residual_centralizer_le_pair)).mpr
      (d.pair_normalizes_U_of_normal g hU)

public theorem Context.centralizer_le_complementFusionGroup_of_normal
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal) :
    centralizer (residualGenerated M z t : Set G) ≤ complementFusionGroup g := by
  have hJA : centralizer (residualGenerated M z t : Set G) ≤
      centralizer (closure (Z ∩ (M : Set G)) : Set G) :=
    centralizer_le d.distinguished_le_residual
  exact le_inf (le_inf (d.residual_centralizer_le_pair.trans inf_le_left) hJA)
    ((le_inf (hJA.trans (Subgroup.centralizer_le_normalizer _))
      ((normal_subgroupOf_iff_le_normalizer g.U_le_centralizer).mp hU)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _))

public theorem Context.local_normalizer_preserves_closure_sup_U_of_normal
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal) :
    M ⊓ normalizer (residualGenerated M z t : Set G) ≤
      normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hMN, _⟩ :=
    proper_residualGenerated_structure d.minimal d.reduction d.action
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper d.even_pair
  have hPN : borelTwoCore M z t ≤
      normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [d.centralizer_closure_sup_U g, g.P_eq]
    exact inf_le_left
  have hDN : residualPairStabilizer M t ≤
      normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) := by
    apply le_trans (le_inf ?_ (d.pair_normalizes_U_of_normal g hU))
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
    rw [distinguishedClosure_normalizer d.minimal.disconnected]
    exact inf_le_left
  intro x hx
  have hx' : x ∈ (borelTwoCore M z t : Set G) * (residualPairStabilizer M t : Set G) :=
    hMN ▸ hx
  obtain ⟨p, hp, v, hv, rfl⟩ := hx'
  exact mul_mem (hPN hp) (hDN hv)

public theorem Context.complementFusionGroup_eq_product (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal)
    (Y : Subgroup G) (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hJ : (centralizer (residualGenerated M z t : Set G) : Set G) =
      (g.U : Set G) * (Y : Set G)) :
    (complementFusionGroup g : Set G) = (g.S : Set G) * (Y : Set G) := by
  have hSR := s.S_le_complementFusionGroup g
  have hJR := d.centralizer_le_complementFusionGroup_of_normal g hU
  apply Set.Subset.antisymm
  · intro x hx
    have hxN : x ∈ normalizer (g.T : Set G) :=
      d.normalizer_closure_sup_U_eq g ▸ hx.2
    have hxprod : x ∈ (g.S : Set G) *
        ((residualPairStabilizer M t ⊓ normalizer (g.U : Set G) : Subgroup G) : Set G) :=
      s.normalizer_product ▸ hxN
    obtain ⟨a, ha, b, hb, rfl⟩ := hxprod
    have hbC : b ∈ centralizer (closure (Z ∩ (M : Set G)) : Set G) := by
      simpa using (centralizer (closure (Z ∩ (M : Set G)) : Set G)).mul_mem
        ((centralizer (closure (Z ∩ (M : Set G)) : Set G)).inv_mem (hSR ha).1.2) hx.1.2
    have hbJ : b ∈ centralizer (residualGenerated M z t : Set G) :=
      d.pair_inf_distinguished_centralizer g ▸ (show b ∈
        residualPairStabilizer M t ⊓ centralizer (closure (Z ∩ (M : Set G)) : Set G) from
          ⟨hb.1, hbC⟩)
    have hbprod : b ∈ (g.U : Set G) * (Y : Set G) := hJ ▸ hbJ
    obtain ⟨u, hu, y, hy, rfl⟩ := hbprod
    exact ⟨a * u, g.S.mul_mem ha (g.U_le_S hu), y, hy, mul_assoc _ _ _⟩
  · rintro x ⟨a, ha, y, hy, rfl⟩
    exact (complementFusionGroup g).mul_mem (hSR ha) (hJR (hYJ hy))

public theorem Context.complementFusionGroup_le_normalizer_S (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    complementFusionGroup g ≤ normalizer (g.S : Set G) := by
  have hSN : g.S ≤ normalizer (g.T : Set G) :=
    (normal_subgroupOf_iff_le_normalizer g.T_lt_S.le).mp s.T_normal
  apply le_trans ?_ ((normal_subgroupOf_iff_le_normalizer hSN).mp s.S_normal)
  rw [← d.normalizer_closure_sup_U_eq g]
  exact inf_le_right

public theorem Context.complementFusionGroup_solvable_of_normal (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal) :
    Group.IsSolvable (complementFusionGroup g) := by
  let J := centralizer (residualGenerated M z t : Set G)
  have hprod : (J : Set G) = (g.U : Set G) * (J : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨1, g.U.one_mem, x, hx, one_mul x⟩
    · rintro _ ⟨u, hu, j, hj, rfl⟩
      exact J.mul_mem (g.U_le_centralizer hu) hj
  have hn := (d.centralizer_le_complementFusionGroup_of_normal g hU).trans
    (d.complementFusionGroup_le_normalizer_S g s)
  have he : complementFusionGroup g = g.S ⊔ J := by
    apply SetLike.coe_injective
    rw [d.complementFusionGroup_eq_product g s hU J le_rfl hprod,
      coe_mul_of_right_le_normalizer_left g.S J hn]
  obtain ⟨V, hV⟩ := s.S_sylow
  have hp : IsPGroup 2 g.S := hV ▸ V.isPGroup'
  let := hp.isNilpotent
  let := g.centralizer_solvable
  rw [he]
  exact Group.isSolvable_sup_of_normalizes g.S J hn

public theorem Context.complementFusionGroup_hall_of_normal (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal)
    (Y : Subgroup G) (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hodd : Odd (Nat.card Y))
    (hJ : (centralizer (residualGenerated M z t : Set G) : Set G) =
      (g.U : Set G) * (Y : Set G)) :
    IsHallSubgroup {p : Nat.Primes | p.val ≠ 2}
      (Y.subgroupOf (complementFusionGroup g)) := by
  have hYR := hYJ.trans (d.centralizer_le_complementFusionGroup_of_normal g hU)
  have hcardY : Nat.card (Y.subgroupOf (complementFusionGroup g)) = Nat.card Y :=
    Nat.card_congr (subgroupOfEquivOfLe hYR).toEquiv
  obtain ⟨V, hV⟩ := s.S_sylow
  have hp : IsPGroup 2 g.S := hV ▸ V.isPGroup'
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hdisj : Disjoint g.S Y := disjoint_of_coprime_natCard (by
    rw [hk]; exact hodd.coprime_two_left.pow_left k)
  have hc := card_set_mul_mul_card_inf g.S Y
  rw [← d.complementFusionGroup_eq_product g s hU Y hYJ hJ,
    hdisj.eq_bot, card_bot, mul_one] at hc
  change Nat.card (complementFusionGroup g) = Nat.card g.S * Nat.card Y at hc
  have hi : (Y.subgroupOf (complementFusionGroup g)).index = 2 ^ k := by
    have hh := (Y.subgroupOf (complementFusionGroup g)).card_mul_index
    rw [hcardY, hc, hk, Nat.mul_comm (2 ^ k)] at hh
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hh
  refine ⟨?_, ?_⟩
  · intro p hp heq
    rw [hcardY, heq] at hp
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hp)
  · intro p hp hne
    rw [hi] at hp
    exact hne ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow hp))

public theorem complement_conjugate_eq_of_normal_complement
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : (g.U.subgroupOf (centralizer (residualGenerated M z t : Set G))).Normal)
    (E Y : Subgroup G) (hYJ : Y ≤ centralizer (residualGenerated M z t : Set G))
    (hYne : Y ≠ ⊥) (hodd : Odd (Nat.card Y))
    (hJ : (centralizer (residualGenerated M z t : Set G) : Set G) =
      (g.U : Set G) * (Y : Set G))
    (hYE : Y ≤ normalizer (E : Set G))
    (x : G) (hxM : x ∈ M)
    (hEF : E.conjBy x = closure (Z ∩ (M : Set G)) ⊔ g.U) :
    E = closure (Z ∩ (M : Set G)) ⊔ g.U := by
  exact complement_conjugate_eq_of_hall g s E Y hYJ hYne hYE
    (hYJ.trans (d.centralizer_le_complementFusionGroup_of_normal g hU))
    (d.complementFusionGroup_solvable_of_normal g s hU)
    (d.complementFusionGroup_hall_of_normal g s hU Y hYJ hodd hJ)
    (d.local_normalizer_preserves_closure_sup_U_of_normal g hU) x hxM hEF

end BenderSuzuki.ZD.SuzukiExclusion

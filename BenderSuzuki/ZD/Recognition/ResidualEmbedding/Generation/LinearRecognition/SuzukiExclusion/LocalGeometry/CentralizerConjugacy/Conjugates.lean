module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Borel
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.LocalGeometry.Stages

/-!
# Displacing the Suzuki centralizer Sylow factor

Choose y in S outside T with y² in T. The normalizer-control premise makes
U and yUy⁻¹ disjoint. The latter subgroup contains no distinguished
involution, so it also meets P trivially. Both factors are normal relative
to T; hence yUy⁻¹ centralizes P. Writing an element as pu in T = PU
then puts p in Z(P) = A, so its square lies in U ∩ yUy⁻¹ and is trivial.
Conjugation transfers exponent two back to U.

Source: GLS4, Chapter 2, Lemma 14.3(b). All conjugates here mean yUy⁻¹,
the literal `MulAut.conj y` convention. The normalizer control is an
explicit preceding-source premise, to be discharged by the parent.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup PFAppendixIII BenderSuzuki.MatrixGroups
open scoped Pointwise
variable {G : Type*} [Group G] {M : Subgroup G} {z t : G}

namespace SylowConfiguration
variable (c : SylowConfiguration M z t)
include c

public theorem U_le_T : c.U ≤ c.T := by rw [c.U_eq]; exact inf_le_left
public theorem U_le_J : c.U ≤ centralizer (residualGenerated M z t : Set G) := by
  rw [c.U_eq]; exact inf_le_right
public theorem P_le_T : borelTwoCore M z t ≤ c.T := by rw [c.P_eq]; exact inf_le_left
public theorem P_le_L : borelTwoCore M z t ≤ residualGenerated M z t := by
  rw [c.P_eq]; exact inf_le_right
public theorem T_le_normalizer : c.T ≤ normalizer (residualGenerated M z t : Set G) := by
  obtain ⟨V, hV⟩ := c.T_sylow
  rw [← hV]
  exact map_subtype_le _
public theorem S_le_normalizer : c.S ≤ normalizer (c.T : Set G) := by
  obtain ⟨V, hV⟩ := c.S_sylow
  rw [← hV]
  exact map_subtype_le _
public theorem T_isPGroup : IsPGroup 2 c.T := by
  obtain ⟨V, hV⟩ := c.T_sylow
  rw [← hV]
  exact V.isPGroup'.map _
public theorem S_isPGroup : IsPGroup 2 c.S := by
  obtain ⟨V, hV⟩ := c.S_sylow
  rw [← hV]
  exact V.isPGroup'.map _
public theorem U_le_pair : c.U ≤ residualPairStabilizer M t := by
  obtain ⟨V, hV⟩ := c.U_sylow_pair
  rw [← hV]
  exact map_subtype_le _

public theorem T_normalizes_U : c.T ≤ normalizer (c.U : Set G) := by
  rw [c.U_eq]
  apply le_trans (le_inf c.T.le_normalizer ?_) inf_normalizer_le_normalizer_inf
  exact c.T_le_normalizer.trans
    ((normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp inferInstance)

public theorem T_normalizes_P : c.T ≤ normalizer (borelTwoCore M z t : Set G) := by
  rw [c.P_eq]
  exact (le_inf c.T.le_normalizer c.T_le_normalizer).trans inf_normalizer_le_normalizer_inf

public theorem S_inf_normalizer : c.S ⊓ normalizer (residualGenerated M z t : Set G) ≤ c.T := by
  let N := normalizer (residualGenerated M z t : Set G)
  obtain ⟨V, hV⟩ := c.T_sylow
  have hTV : c.T.subgroupOf N = V := by
    rw [← hV]
    exact comap_map_eq_self (by simp)
  have hSN : c.S.subgroupOf N ≤ normalizer (V : Set N) := by
    change c.S.subgroupOf N ≤ normalizer ((V : Subgroup N) : Set N)
    rw [← hTV, ← subgroupOf_normalizer_eq c.T_le_normalizer]
    exact comap_mono c.S_le_normalizer
  have hSV : c.S.subgroupOf N ≤ V := by
    have hh := (c.S_isPGroup.comap_subtype (K := N)).inf_normalizer_sylow V
    change c.S.subgroupOf N ⊓ normalizer (V : Set N) = c.S.subgroupOf N ⊓ V at hh
    rw [inf_eq_left.mpr hSN] at hh
    exact (inf_eq_left.mp hh.symm)
  intro x hx
  have hxV := hSV (show (⟨x, hx.2⟩ : N) ∈ c.S.subgroupOf N from hx.1)
  rw [← hV]
  exact ⟨⟨x, hx.2⟩, hxV, rfl⟩

public theorem exists_square_in_T : ∃ y ∈ c.S, y ∉ c.T ∧ y ^ 2 ∈ c.T := by
  have step : ∀ n : ℕ, ∀ x ∈ c.S, x ∉ c.T → x ^ (2 ^ n) ∈ c.T →
      ∃ y ∈ c.S, y ∉ c.T ∧ y ^ 2 ∈ c.T := by
    intro n
    induction n with
    | zero => intro x _ hx hn; exact (hx (by simpa using hn)).elim
    | succ n ih =>
      intro x hx hn hp
      by_cases hs : x ^ 2 ∈ c.T
      · exact ⟨x, hx, hn, hs⟩
      · apply ih (x ^ 2) (c.S.pow_mem hx 2) hs
        rw [← pow_mul, ← pow_succ']
        exact hp
  obtain ⟨x, hxS, hxT⟩ := SetLike.exists_of_lt c.T_lt_S
  obtain ⟨n, hn⟩ := c.S_isPGroup ⟨x, hxS⟩
  exact step n x hxS hxT (by
    have he : x ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    rw [he]
    exact c.T.one_mem)

public theorem disjoint_conjugate_U
    (hcontrol : ∀ Y : Subgroup G,
      Y ≤ centralizer (residualGenerated M z t : Set G) → Y ≠ ⊥ →
        normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G))
    {y : G} (hyS : y ∈ c.S) (hyT : y ∉ c.T) (hy2 : y ^ 2 ∈ c.T) :
    Disjoint c.U (c.U.map (MulAut.conj y).toMonoidHom) := by
  let f := (MulAut.conj y).toMonoidHom
  have hyU2 : (c.U.map f).map f = c.U := by
    rw [map_map]
    have he : f.comp f = (MulAut.conj (y ^ 2)).toMonoidHom := by
      ext x
      simp [f, MulAut.conj_apply, pow_two, mul_assoc]
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp (c.T_normalizes_U hy2)
  have hyI : y ∈ normalizer ((c.U ⊓ c.U.map f : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change (c.U ⊓ c.U.map f).map f = c.U ⊓ c.U.map f
    rw [map_inf _ _ _ (MulAut.conj y).injective, hyU2, inf_comm]
  by_contra hd
  have hne : c.U ⊓ c.U.map f ≠ ⊥ := fun h => hd (disjoint_iff.mpr h)
  exact hyT (c.S_inf_normalizer ⟨hyS, hcontrol _ (inf_le_left.trans c.U_le_J) hne hyI⟩)
end SylowConfiguration

variable [Finite G] {Z : Set G} {m : ℕ} (d : Context Z M z t m)
include d

/-- Distinguished-involution exclusion separates P from every conjugate of U. -/
public theorem Context.disjoint_P_conjugate_U (c : SylowConfiguration M z t) (y : G) :
    Disjoint (borelTwoCore M z t) (c.U.map (MulAut.conj y).toMonoidHom) := by
  let V := c.U.map (MulAut.conj y).toMonoidHom
  have hVZ : ∀ v ∈ V, v ∉ Z := by
    rintro _ ⟨u, hu, rfl⟩ hvZ
    apply not_mem_Z_of_mem_residualPairStabilizer d.minimal.disconnected
      d.t_not_mem_M (c.U_le_pair hu)
    have hh := d.minimal.disconnected.invariant y⁻¹ (MulAut.conj y u) hvZ
    simpa only [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh
  by_contra hd
  let I := borelTwoCore M z t ⊓ V
  have hne : I ≠ ⊥ := fun h => hd (disjoint_iff.mpr h)
  let : Nontrivial I := (nontrivial_iff_ne_bot I).mpr hne
  have hI : IsPGroup 2 I := (c.T_isPGroup.to_le c.P_le_T).to_inf_left
  obtain ⟨n, hn, hcard⟩ := hI.nontrivial_iff_card.mp inferInstance
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := I) 2
    (hcard ▸ dvd_pow_self 2 (Nat.ne_of_gt hn))
  have hi : PFAppendixIII.IsInvolution (a : G) :=
    IsInvolution.map_of_injective (orderOf_eq_prime_iff.mp ha).symm I.subtype Subtype.val_injective
  exact hVZ a a.property.2
    ((isInvolution_iff_mem_Z_in_proper_residualGenerated d.minimal.disconnected d.reduction
      d.z_mem d.z_mem_M d.t_mem d.t_not_mem_M d.proper (c.P_le_L a.property.1)).mp hi)

/-- The conjugate-factor argument of Lemma 14.3(b), without using any
centralizer equality that presupposes involutions in U. -/
public theorem Context.U_elementary (c : SylowConfiguration M z t)
    (hcontrol : ∀ Y : Subgroup G,
      Y ≤ centralizer (residualGenerated M z t : Set G) → Y ≠ ⊥ →
        normalizer (Y : Set G) ≤ normalizer (residualGenerated M z t : Set G)) :
    IsElementaryAbelian 2 c.U := by
  obtain ⟨y, hyS, hyT, hy2⟩ := c.exists_square_in_T
  let f := (MulAut.conj y).toMonoidHom
  let V := c.U.map f
  have hyN := c.S_le_normalizer hyS
  have hyTeq : c.T.map f = c.T := mem_normalizer_iff_map_conj_eq.mp hyN
  have hVT : V ≤ c.T := by
    rw [← hyTeq]
    exact map_mono c.U_le_T
  have hTN : c.T ≤ normalizer (V : Set G) := by
    rw [← hyTeq]
    exact (map_mono c.T_normalizes_U).trans (le_normalizer_map f)
  have hdUV : Disjoint c.U V := c.disjoint_conjugate_U hcontrol hyS hyT hy2
  have hdPV : Disjoint (borelTwoCore M z t) V := d.disjoint_P_conjugate_U c y
  have hVC : V ≤ centralizer (borelTwoCore M z t : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_antisymm ?_ bot_le
    exact (le_inf (le_normalizer_iff_commutator_le_right.mp (hVT.trans c.T_normalizes_P))
      (le_normalizer_iff_commutator_le_left.mp (c.P_le_T.trans hTN))).trans hdPV.le_bot
  have hsquare : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    have hvprod : v ∈ (borelTwoCore M z t : Set G) * (c.U : Set G) := by
      rw [← c.T_product]
      exact hVT hv
    obtain ⟨p, hp, u, hu, he⟩ := Set.mem_mul.mp hvprod
    have huC : u ∈ centralizer (borelTwoCore M z t : Set G) :=
      Subgroup.centralizer_le c.P_le_L (c.U_le_J hu)
    have hpC : p ∈ centralizer (borelTwoCore M z t : Set G) := by
      have hpE : p = v * u⁻¹ := by rw [← he]; group
      rw [hpE]
      exact (centralizer _).mul_mem (hVC hv) ((centralizer _).inv_mem huC)
    have hpA : p ∈ closure (Z ∩ (M : Set G)) := by
      rw [← d.borelTwoCore_center]
      refine ⟨⟨p, hp⟩, mem_center_iff.mpr ?_, rfl⟩
      intro r
      exact Subtype.ext (hpC r r.property)
    have hp2 : p ^ 2 = 1 :=
      ((Set.ext_iff.mp d.borelTwoCore_square_one p).mpr hpA).2
    have hc : Commute p u := c.U_le_J hu p (c.P_le_L hp)
    have hv2 : v ^ 2 = u ^ 2 := by rw [← he, hc.mul_pow, hp2, one_mul]
    exact disjoint_def.mp hdUV (hv2 ▸ c.U.pow_mem hu 2) (V.pow_mem hv 2)
  have hU2 (u : c.U) : u ^ 2 = 1 := by
    apply Subtype.ext
    apply (MulAut.conj y).injective
    change (MulAut.conj y) ((u : G) ^ 2) = (MulAut.conj y) 1
    rw [map_one, map_pow]
    exact hsquare _ (mem_map_of_mem f u.property)
  refine { toIsMulCommutative := ?_
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hU2 }
  exact ⟨⟨fun u v => (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (hU2 x)) u v).eq⟩⟩
end BenderSuzuki.ZD.SuzukiExclusion

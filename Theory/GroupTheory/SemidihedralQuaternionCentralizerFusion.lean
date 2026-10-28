module
public import Theory.GroupTheory.SemidihedralFourSubgroup
public import Theory.GroupTheory.ElementaryFourSylowFusion
public import Theory.GroupTheory.ElementaryCommutingConjugation
public import Theory.GroupTheory.BinaryWeakCoreIsolatedGeometry
public import Mathlib.GroupTheory.Solvable

/-!
# Component separation in semidihedral centralizer fusion

A four-subgroup of `Q` in the component of `B` is enough to transport `B`
by every element of `C_G(Q)`. Conversely, failed transport separates every
such four-subgroup from `B`. In a finite simple group a conjugate of a
four-subgroup enters the component of `B`, with the local centralizer
simultaneously carried into the selected Sylow subgroup. Its conjugator
must lie outside the component stabilizer, while the conjugate of the
entire ambient centralizer lies inside that stabilizer.

The explicit semidihedral presentation supplies the four-subgroup. These
are reductions for the residual semidihedral–quaternion case of the binary
remark after GLS2, Proposition 22.4 (`refs/KGroup/GLS2/ChapterF.tex`). They
do not yet exclude the resulting separation configuration. The ambient
extension used here is GLS4, Lemma 18.1, before the later K-properness
hypothesis (`refs/KGroup/GLS4/Chapter2.tex`).

The nonsolvable generated-envelope hypothesis also forces a proper
nonsolvable involution centralizer containing the chosen Sylow subgroup.
The isolated-four geometry supplies the common central involution; the
entire ambient centralizer of `Q` centralizes it. This is an obstruction
that local solvability hypotheses can exclude, but does not itself prove
transport under the unrestricted hypotheses.
-/

namespace Subgroup

/-- A connected subgroup of `Q` suffices for transport by its centralizer. -/
public theorem elementaryCommutingConnected_conj_of_connected_subgroup
    {G : Type*} [Group G] {p : ℕ} (B Q E : Subgroup G)
    (hEQ : E ≤ Q) (hBE : ElementaryCommutingConnected p B E)
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected p B (B.map (MulAut.conj c).toMonoidHom) := by
  let : IsElementaryAbelian p B := hBE.left.1
  exact normalizer_le_elementaryCommutingStabilizer B E hBE.left.2 hBE
    (centralizer_le_normalizer _ (centralizer_le hEQ hc))

/-- The remaining ambient four-group bridge would give the requested
transport without any normalization assertion about the local centralizer. -/
public theorem elementaryCommutingConnected_conj_of_four_bridge
    {G : Type*} [Group G] (B Q : Subgroup G)
    (hbridge : ∃ E : Subgroup G, E ≤ Q ∧ ElementaryCommutingConnected 2 B E)
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 B (B.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨E, hEQ, hBE⟩ := hbridge
  exact elementaryCommutingConnected_conj_of_connected_subgroup B Q E hEQ hBE c hc

/-- Failure of centralizer transport gives a conjugator outside the main
component stabilizer, carrying the ambient centralizer into that stabilizer
and its local part into the chosen Sylow subgroup. -/
public theorem exists_displacing_four_transport_of_failed_centralizer_transport
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (B Q E : Subgroup G)
    [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 E]
    (hB : 8 ≤ Nat.card B) (hE : Nat.card E = 4)
    (hBS : B ≤ S) (hQS : Q ≤ S) (hEQ : E ≤ Q)
    (c : G) (hc : c ∈ centralizer (Q : Set G))
    (hfail : ¬ ElementaryCommutingConnected 2 B
      (B.map (MulAut.conj c).toMonoidHom)) :
    let M := elementaryCommutingStabilizer 2 B (by omega)
    ¬ ElementaryCommutingConnected 2 B E ∧
      (S : Subgroup G) ≤ M ∧ M ≠ ⊤ ∧
      ∃ g : G, g ∉ M ∧
        ElementaryCommutingConnected 2 B (E.map (MulAut.conj g).toMonoidHom) ∧
        (centralizer (Q : Set G)).map (MulAut.conj g).toMonoidHom ≤ M ∧
        ((S : Subgroup G) ⊓ centralizer (Q : Set G)).map
          (MulAut.conj g).toMonoidHom ≤ S := by
  let M := elementaryCommutingStabilizer 2 B (by omega)
  have hnot : ¬ ElementaryCommutingConnected 2 B E := fun h =>
    hfail (elementaryCommutingConnected_conj_of_connected_subgroup B Q E hEQ h c hc)
  refine ⟨hnot, twoGroup_le_elementaryCommutingStabilizer _ B S.isPGroup' hB hBS,
    ?_, ?_⟩
  · intro htop
    apply hfail
    change c ∈ elementaryCommutingStabilizer 2 B (by omega)
    rw [htop]
    exact mem_top c
  obtain ⟨g, hgE, hgC⟩ :=
    exists_conj_four_connected_with_sylow_centralizer_of_simple S B E hB hE
      hBS (hEQ.trans hQS)
  refine ⟨g, ?_, hgE, ?_, ?_⟩
  · intro hg
    have hBg : ElementaryCommutingConnected 2 B
        (B.map (MulAut.conj g).toMonoidHom) := hg
    exact hnot ((elementaryCommutingConnected_map_iff 2 (MulAut.conj g) B E).mp
      (hBg.symm.trans hgE))
  · have hmap : (centralizer (Q : Set G)).map (MulAut.conj g).toMonoidHom ≤
        centralizer (E.map (MulAut.conj g).toMonoidHom : Set G) := by
      rintro x ⟨y, hy, rfl⟩ e ⟨v, hv, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, map_mul] using
        congrArg (MulAut.conj g) (hy v (hEQ hv))
    exact hmap.trans ((centralizer_le_normalizer _).trans
      (normalizer_le_elementaryCommutingStabilizer B _ (by omega) hgE))
  · exact (map_mono (inf_le_inf_left _ (centralizer_le hEQ))).trans hgC

/-- The semidihedral presentation supplies an actual four-group to which
the failed-transport separation argument applies. -/
public theorem semidihedral_exists_displacing_four_of_failed_transport
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (B Q : Subgroup G) [IsElementaryAbelian 2 B]
    (hB : 8 ≤ Nat.card B) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ ((S : Subgroup G) ⊓ centralizer (Q : Set G)))
    (hsd : ∃ n : ℕ, 4 ≤ n ∧ Nat.card Q = 2 ^ n ∧
      ∃ a b : Q, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧ closure ({a, b} : Set Q) = ⊤)
    (c : G) (hc : c ∈ centralizer (Q : Set G))
    (hfail : ¬ ElementaryCommutingConnected 2 B
      (B.map (MulAut.conj c).toMonoidHom)) :
    let M := elementaryCommutingStabilizer 2 B (by omega)
    ∃ E : Subgroup G, IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧ E ≤ Q ∧
      ¬ ElementaryCommutingConnected 2 B E ∧
      (S : Subgroup G) ≤ M ∧ M ≠ ⊤ ∧
      ∃ g : G, g ∉ M ∧
        ElementaryCommutingConnected 2 B (E.map (MulAut.conj g).toMonoidHom) ∧
        (centralizer (Q : Set G)).map (MulAut.conj g).toMonoidHom ≤ M ∧
        ((S : Subgroup G) ⊓ centralizer (Q : Set G)).map
          (MulAut.conj g).toMonoidHom ≤ S := by
  obtain ⟨n, hn, -, a, b, ha, hb, hconj, hgen⟩ := hsd
  obtain ⟨E, hEe, hE, hEQ⟩ := Semidihedral.exists_four_le Q hn a b ha hb hconj hgen
  let : IsElementaryAbelian 2 E := hEe
  exact ⟨E, hEe, hE, hEQ,
    exists_displacing_four_transport_of_failed_centralizer_transport S B Q E hB hE
      (hBweak.trans (sup_le hQS inf_le_left)) hQS hEQ c hc hfail⟩

/-- The nonsolvable generated-envelope residual forces a proper nonsolvable
involution centralizer containing the selected Sylow subgroup. -/
public theorem semidihedral_residual_nonsolvable_involution_centralizer
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (B Q : Subgroup G) [IsElementaryAbelian 2 B]
    (hB : 8 ≤ Nat.card B) (hQS : Q ≤ S)
    (hBweak : B ≤ Q ⊔ ((S : Subgroup G) ⊓ centralizer (Q : Set G)))
    (hsd : ∃ n : ℕ, 4 ≤ n ∧ Nat.card Q = 2 ^ n ∧
      ∃ a b : Q, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧ closure ({a, b} : Set Q) = ⊤)
    (hiso : ∀ V : Subgroup G, IsElementaryAbelian 2 V → Nat.card V = 4 →
      V ≤ Q → ∀ W : Subgroup G, IsElementaryAbelian 2 W → Nat.card W = 4 →
      W ≤ S → W ≤ centralizer (V : Set G) → W = V)
    (hunique : ∃! t : centralizer (Q : Set G), orderOf t = 2)
    (c : G) (hc : c ∈ centralizer (Q : Set G))
    (henv : ¬ Group.IsSolvable
      (((S : Subgroup G) ⊓ centralizer (Q : Set G)) ⊔ zpowers c : Subgroup G)) :
    ∃ z : G, orderOf z = 2 ∧ z ∈ Q ∧
      (S : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      centralizer (Q : Set G) ≤ centralizer ({z} : Set G) ∧
      centralizer ({z} : Set G) ≠ ⊤ ∧
      ¬ Group.IsSolvable (centralizer ({z} : Set G)) := by
  obtain ⟨n, hn, -, a, b, ha, hb, hconj, hgen⟩ := hsd
  obtain ⟨E, hEe, hE, hEQ⟩ := Semidihedral.exists_four_le Q hn a b ha hb hconj hgen
  let : IsElementaryAbelian 2 E := hEe
  obtain ⟨z, hz, -, hzQ, hzS, hCz⟩ :=
    central_involution_of_isolated_four_of_unique_centralizer (S : Subgroup G) B Q E
      S.isPGroup' hB hE (hBweak.trans (sup_le hQS inf_le_left)) hQS hEQ
      (hiso E hEe hE hEQ) hunique
  have hLz : ((S : Subgroup G) ⊓ centralizer (Q : Set G)) ⊔ zpowers c ≤
      centralizer ({z} : Set G) :=
    (sup_le inf_le_right (zpowers_le.mpr hc)).trans hCz
  have hnsolv : ¬ Group.IsSolvable (centralizer ({z} : Set G)) := by
    intro hs
    let := hs
    exact henv (Group.isSolvable_of_isSolvable_injective (inclusion_injective hLz))
  refine ⟨z, hz, hzQ, ?_, hCz, ?_, hnsolv⟩
  · intro s hs
    exact mem_centralizer_singleton_iff.mpr (hzS s hs)
  · intro htop
    have hzZ : z ∈ center G := mem_center_iff.mpr fun g =>
      mem_centralizer_singleton_iff.mp (htop ▸ mem_top g)
    have hZ : center G = ⊤ :=
      (inferInstance : (center G).Normal).eq_bot_or_eq_top.resolve_left (by
        intro hbot
        have hz1 : z = 1 := mem_bot.mp (hbot ▸ hzZ)
        simp [hz1] at hz)
    let : Group.IsSolvable G := Group.isSolvable_of_comm fun x y =>
      mem_center_iff.mp (hZ ▸ mem_top y) x
    exact hnsolv (Group.isSolvable_of_isSolvable_injective
      (centralizer ({z} : Set G)).subtype_injective)

end Subgroup

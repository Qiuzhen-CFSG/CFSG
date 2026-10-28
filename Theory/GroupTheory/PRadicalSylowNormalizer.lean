module

public import Theory.GroupTheory.PRadical
public import Theory.GroupTheory.SylowKernelCore

/-!
# Moving radical subgroups into a fixed Sylow subgroup

If a radical p-subgroup has normalizer of index prime to p, a Sylow subgroup
of that normalizer is Sylow in the ambient group. The radical subgroup lies
in its normalizer's intrinsic p-core, hence in this Sylow subgroup. Sylow
conjugacy therefore moves it to a subgroup of any fixed Sylow subgroup that
is normalized by that fixed subgroup. Radicality is preserved by this move.

We also record the normalizer-condition criterion: a self-normalizing
p-subgroup of a finite group is Sylow. It allows a local normalizer
calculation to establish Sylow status without computing the ambient order.

Source application: Aschbacher--Smith, proof of Proposition 1.3.4, printed
p.511 (PDF p.528), using the Sylow-overgroup analysis in [Asc86b]. These
are general finite-group reductions, not the sporadic-group calculation.
-/

namespace Subgroup

variable {G H : Type*} [Group G] [Group H] {p : ℕ}

/-- An isomorphism preserves radicality, including the intrinsic normalizer
p-core and its embedding in the ambient group. -/
public theorem IsPRadical.map_equiv {U : Subgroup G} (hU : U.IsPRadical p)
    (e : G ≃* H) : (U.map e.toMonoidHom).IsPRadical p := by
  refine ⟨fun h => hU.1 ((U.map_eq_bot_iff_of_injective e.injective).mp h), ?_⟩
  change (normalizer (U.map e.toMonoidHom : Set H)).pCoreIn p = U.map e.toMonoidHom
  rw [← map_equiv_normalizer_eq U e, ← map_pCoreIn_of_injective p _ _ e.injective]
  exact congrArg (fun V : Subgroup G => V.map e.toMonoidHom) hU.2

variable [Finite G] [Fact p.Prime]

/-- A self-normalizing p-subgroup is Sylow: its normalizer inside any
containing Sylow subgroup is itself, so the p-group normalizer condition
forces equality. -/
public theorem exists_sylow_eq_of_isPGroup_of_normalizer_eq (P : Subgroup G)
    (hP : IsPGroup p P) (hnorm : normalizer (P : Set G) = P) :
    ∃ S : Sylow p G, (S : Subgroup G) = P := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  have hn : normalizer (P.subgroupOf (S : Subgroup G) : Set S) =
      P.subgroupOf (S : Subgroup G) := by
    rw [← subgroupOf_normalizer_eq hPS, hnorm]
  have ht : P.subgroupOf (S : Subgroup G) = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := S)) _ hn
  exact ⟨S, le_antisymm (subgroupOf_eq_top.mp ht) hPS⟩

/-- A radical subgroup with normalizer of index prime to p is conjugate
to a subgroup normal in any prescribed Sylow p-subgroup. Normality here
is relative to the Sylow subgroup, expressed by the two inclusions. -/
public theorem IsPRadical.exists_conjugate_le_and_le_normalizer
    {U : Subgroup G} (hU : U.IsPRadical p) (S : Sylow p G)
    (hindex : ¬ p ∣ (normalizer (U : Set G)).index) :
    ∃ g : G, U.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ normalizer (U.map (MulAut.conj g).toMonoidHom : Set G) := by
  let N := normalizer (U : Set G)
  let Q : Sylow p N := Sylow.nonempty.some
  have hQindex : ¬ p ∣ ((Q : Subgroup N).map N.subtype).index := by
    rw [index_map_subtype]
    exact (Fact.out : p.Prime).not_dvd_mul Q.not_dvd_index hindex
  let T : Sylow p G := (Q.isPGroup'.map N.subtype).toSylow hQindex
  have hUT : U ≤ (T : Subgroup G) := by
    rw [← hU.2]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal Q)
  have hTN : (T : Subgroup G) ≤ N := map_subtype_le _
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hmap : (T : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) := by
    change ((g • T : Sylow p G) : Subgroup G) = (S : Subgroup G)
    exact congrArg (fun P : Sylow p G => (P : Subgroup G)) hg
  refine ⟨g, (map_mono hUT).trans_eq hmap, ?_⟩
  rw [← map_equiv_normalizer_eq U (MulAut.conj g), ← hmap]
  exact map_mono hTN

end Subgroup

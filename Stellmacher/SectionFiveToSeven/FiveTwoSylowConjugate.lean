module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.BaumannTwoOvergroupNormalizer

/-!
# A Baumann-normalizer Sylow conjugate

Let `S` be a global Sylow 2-subgroup and let `Q ≤ N` be a 2-subgroup
containing the Baumann subgroup `B(S)`.  There is an element `h` normalizing
`B(S)` such that `S^h ∩ N` is a Sylow 2-subgroup of `N`.

Extend `Q` first to a Sylow 2-subgroup of `N` and then to a global Sylow
2-subgroup `U`.  Both `S` and `U` contain `B(S)`, so the Baumann weak-closure
normalizer theorem puts both inside `N_G(B(S))`.  Sylow conjugacy inside that
normalizer gives `S^h=U`; maximality of the original Sylow subgroup of `N`
then identifies `U∩N` with it.

This is the Sylow-conjugacy construction used in the proof of assertion (3)
of Stellmacher (5.2), Journal of Algebra 190 (1997), p. 28.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

universe u

/-! Choose the conjugate Sylow subgroup in the normalizer of the Baumann
subgroup. -/
public theorem exists_sylow_inter_baumann_conjugate
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (N Q : Subgroup G)
    (hQp : IsPGroup 2 Q) (hQN : Q ≤ N)
    (hBQ : baumannIn (S : Subgroup G) ≤ Q) :
    ∃ h : G,
      h ∈ Subgroup.normalizer (baumannIn (S : Subgroup G) : Set G) ∧
      Q ≤ (S : Subgroup G).map (MulAut.conj h).toMonoidHom ∧
      IsSylowTwoIn
        (((S : Subgroup G).map (MulAut.conj h).toMonoidHom) ⊓ N) N := by
  classical
  let B : Subgroup G := baumannIn (S : Subgroup G)
  let QN : Subgroup N := Q.subgroupOf N
  have hQNp : IsPGroup 2 QN :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  obtain ⟨T, hQNT⟩ := hQNp.exists_le_sylow
  let Ta : Subgroup G := (T : Subgroup N).map N.subtype
  have hQTa : Q ≤ Ta := by
    calc
      Q = QN.map N.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQN).symm
      _ ≤ (T : Subgroup N).map N.subtype := Subgroup.map_mono hQNT
      _ = Ta := rfl
  have hTap : IsPGroup 2 Ta := T.isPGroup'.map N.subtype
  obtain ⟨U, hTaU⟩ := hTap.exists_le_sylow
  have hBU : B ≤ (U : Subgroup G) := (hBQ.trans hQTa).trans hTaU
  have hUNB : (U : Subgroup G) ≤ Subgroup.normalizer (B : Set G) := by
    simpa [B, baumannIn, omegaOneCenter,
      Stellmacher.omegaOneCenterAmbient] using
      (Stellmacher.twoSubgroup_le_normalizer_baumann S (U : Subgroup G)
        U.isPGroup' (by
          simpa [B, baumannIn, omegaOneCenter,
            Stellmacher.omegaOneCenterAmbient] using hBU))
  have hSNB : (S : Subgroup G) ≤ Subgroup.normalizer (B : Set G) := by
    simpa [B, baumannIn, omegaOneCenter,
      Stellmacher.omegaOneCenterAmbient] using
      (Stellmacher.twoSubgroup_le_normalizer_baumann S (S : Subgroup G)
        S.isPGroup' inf_le_left)
  let NB : Subgroup G := Subgroup.normalizer (B : Set G)
  let SNB : Sylow 2 NB := S.subtype hSNB
  let UNB : Sylow 2 NB := U.subtype hUNB
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq NB SNB UNB
  let h : G := (n : NB)
  have hh : h ∈ Subgroup.normalizer (B : Set G) := n.property
  have hmap : (S : Subgroup G).map (MulAut.conj h).toMonoidHom =
      (U : Subgroup G) := by
    have hnsyl : (n • S).subtype (Sylow.smul_le hSNB n) =
        U.subtype hUNB := by
      rw [← S.smul_subtype hSNB n]
      exact hn
    have hcoe := congrArg
      (fun R : Sylow 2 NB ↦ (R : Subgroup NB).map NB.subtype) hnsyl
    rw [Sylow.coe_subtype, Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le (Sylow.smul_le hSNB n),
      Subgroup.map_subgroupOf_eq_of_le hUNB] at hcoe
    change (((n : G) • S : Sylow 2 G) : Subgroup G) =
      (U : Subgroup G) at hcoe
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hcoe
    have hend :
        (MulDistribMulAction.toMonoidEnd (MulAut G) G) (MulAut.conj (n : G)) =
          (MulAut.conj (n : G)).toMonoidHom := by
      ext x
      rfl
    rw [hend] at hcoe
    simpa [h] using hcoe
  have hTaN : Ta ≤ N := Subgroup.map_subtype_le (T : Subgroup N)
  have hTinf : Ta = (U : Subgroup G) ⊓ N := by
    apply le_antisymm
    · exact le_inf hTaU hTaN
    · have hinfp : IsPGroup 2 ↑((U : Subgroup G) ⊓ N) :=
        U.isPGroup'.to_le inf_le_left
      have hsubp : IsPGroup 2 (((U : Subgroup G) ⊓ N).subgroupOf N) :=
        hinfp.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      have hTsub : (T : Subgroup N) ≤
          ((U : Subgroup G) ⊓ N).subgroupOf N := by
        intro x hx
        exact ⟨hTaU (Subgroup.mem_map_of_mem N.subtype hx), x.property⟩
      have hsubT : ((U : Subgroup G) ⊓ N).subgroupOf N ≤ (T : Subgroup N) :=
        (T.3 hsubp hTsub).le
      simpa [Ta] using Subgroup.map_mono (f := N.subtype) hsubT
  refine ⟨h, by simpa [B] using hh, ?_, ?_⟩
  · rw [hmap]
    exact (hQTa.trans hTaU)
  refine ⟨inf_le_right, T, ?_⟩
  change Ta = (S : Subgroup G).map (MulAut.conj h).toMonoidHom ⊓ N
  rw [hmap]
  exact hTinf

end Stellmacher.SectionsFiveToSeven

module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Centralizer.SourceInterfaces
public import Theory.SpecificGroups.SL2.SubgroupTwoCore
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent

/-!
# The two-subgroups of the actual linear centralizer

The supplied injective homomorphism from J=C_G(L) into the marked binary
PSL₂ group lifts through the characteristic-two SL₂/PSL₂ isomorphism.
Every two-subgroup of J is consequently elementary abelian. If O₂(J) is
nontrivial, the intrinsic SL₂ normalizer calculation puts every two-subgroup
of J in O₂(J), so this core is Sylow. The actual pair-stabilizer involutions
centralize L by source 12.9 and therefore lie in the embedded core.

Nontriviality of O₂(J) is an explicit premise here, to be discharged by
Lemma 15.4. No centralizer order, odd supplement or later counting result
is assumed. These are the intrinsic model consequences used between
Lemmas 15.4 and 15.5 in refs/KGroup/GLS4/Chapter2.tex.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "L" => residualGenerated M z t
local notation "J" => centralizer (L : Set G)

private def linearEmbedding (hm : CentralizerLocalModelData d) :
    J →* Converse.SL2 (BinaryGaloisField n) :=
  let q : Converse.SL2 (BinaryGaloisField n) ≃*
      MatrixGroups.PSL2MatrixGroup (BinaryGaloisField n) :=
    MulEquiv.ofBijective (Converse.pi _) ⟨Converse.pi_injective, Converse.pi_surjective⟩
  (d.model.trans q.symm).toMonoidHom.comp hm.embedding

private theorem linearEmbedding_injective (hm : CentralizerLocalModelData d) :
    Function.Injective (linearEmbedding d hm) :=
  (d.model.trans (MulEquiv.ofBijective (Converse.pi _)
    ⟨Converse.pi_injective, Converse.pi_surjective⟩).symm).injective.comp
      hm.embedding_injective

public theorem Context.centralizer_two_subgroup_le_core (hm : CentralizerLocalModelData d)
    (hne : pCore 2 J ≠ ⊥) (B : Subgroup J) (hB : IsPGroup 2 B) :
    B ≤ pCore 2 J := by
  let f := linearEmbedding d hm
  let e : J ≃* f.range := MonoidHom.ofInjective (linearEmbedding_injective d hm)
  have he := pCore_map_iso 2 e
  have hne' : pCore 2 f.range ≠ ⊥ := by
    rw [← he]
    exact fun hb => hne (((pCore 2 J).map_eq_bot_iff_of_injective e.injective).mp hb)
  have hle := Matrix.SpecialLinearGroup.isPGroup_le_twoCore_of_ne_bot
    f.range hne' (B.map e.toMonoidHom) (hB.map e.toMonoidHom)
  rw [← he] at hle
  exact (map_le_map_iff_of_injective e.injective).mp hle

public theorem Context.centralizer_twoCore_sylow (hm : CentralizerLocalModelData d)
    (hne : pCore 2 J ≠ ⊥) :
    ∃ S : Sylow 2 J, (S : Subgroup J) = pCore 2 J := by
  obtain ⟨S, hS⟩ := (pCore_isPGroup (p := 2) (G := J)).exists_le_sylow
  exact ⟨S, le_antisymm (Context.centralizer_two_subgroup_le_core d hm hne S S.isPGroup') hS⟩

public theorem Context.centralizer_two_subgroup_elementary (hm : CentralizerLocalModelData d)
    (B : Subgroup J) (hB : IsPGroup 2 B) : IsElementaryAbelian 2 B := by
  let f := linearEmbedding d hm
  have hs (x : B) : x ^ 2 = 1 := by
    have h := Matrix.SpecialLinearGroup.twoSubgroup_pow_two (B.map f)
      (hB.map f) ⟨f x, ⟨x, x.property, rfl⟩⟩
    apply Subtype.ext
    apply linearEmbedding_injective d hm
    simpa only [map_pow, map_one, coe_pow, coe_one] using congrArg Subtype.val h
  exact { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b).eq⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

public theorem Context.centralizer_twoCore_elementary (hm : CentralizerLocalModelData d) :
    IsElementaryAbelian 2 ((pCore 2 J).map (J).subtype) := by
  let : IsElementaryAbelian 2 (pCore 2 J) := Context.centralizer_two_subgroup_elementary d hm _ pCore_isPGroup
  exact IsElementaryAbelian.map_subtype

public theorem Context.pair_involutions_mem_twoCore (hm : CentralizerLocalModelData d)
    (hne : pCore 2 J ≠ ⊥) {v : G}
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    v ∈ (pCore 2 J).map (J).subtype := by
  let w : J := ⟨v, d.pair_involution_centralizes hvD hv⟩
  have hw : w ^ 2 = 1 := Subtype.ext hv.sq_eq_one
  let : IsElementaryAbelian 2 (zpowers w) := IsElementaryAbelian.zpowers_of_pow_eq_one hw
  have hc := Context.centralizer_two_subgroup_le_core d hm hne (zpowers w) (IsElementaryAbelian.isPGroup 2 _)
  exact ⟨w, hc (mem_zpowers w), rfl⟩
end BenderSuzuki.ZD.LinearExclusion

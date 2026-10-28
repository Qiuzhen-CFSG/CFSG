module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeQuintet
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFourSpace

/-!
# Quintet rigidity for the M22-code radical argument

The intrinsic Sylow catalogue identifies any two elementary rank-five
subgroups in one two-group. The actual pointwise kernel on the geometric
quintet four-space is a two-group, so an odd-order element fixing the full
quintet fixed space is trivial. These statements keep the full outer actor.
The original Chapter 12 radical argument uses them for pair reselection and
for the center of the escaping extraspecial Sylow subgroup.

Source: Aschbacher--Smith H.14.3(1), H.16.3(4), and 8.2.7, printed
pp.397,403,717--718, refs/quasithin.pdf. The underlying Golay constructions
are the existing licensed ATLAS ports; see LICENSES/ATLAS.txt.
-/


public noncomputable section
open Sporadic.Mathieu Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.M22CodeQuintet
open M22ChapterH

/-- The two rank-five actors inside one two-group are the same subgroup. -/
theorem eq_of_common_two_group (A B P : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hP : IsPGroup 2 P) (hAP : A ≤ P) (hBP : B ≤ P)
    (hA : rank A = 5) (hB : rank B = 5) : A = B := by
  obtain ⟨S,hPS⟩ := hP.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq m22PairStabilizer S CompatibleSylow.outer
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom = CompatibleSylow.outer.toSubgroup :=
    congrArg Sylow.toSubgroup hg
  have same (C : Subgroup m22PairStabilizer) [IsElementaryAbelian 2 C]
      (hCP : C ≤ P) (hc : rank C = 5) :
      C.map (MulAut.conj g).toMonoidHom = m22OuterQuintetKernel m22SourceSextet := by
    let : IsElementaryAbelian 2 (C.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
    have hc' : rank (C.map (MulAut.conj g).toMonoidHom) = 5 := by rwa [rank_map_conj]
    have hn : C.map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
      intro he
      rw [he,Representation.BinaryOffender.rank_bot] at hc'
      omega
    have hcard : Nat.card (C.map (MulAut.conj g).toMonoidHom) = 32 := by
      rw [(show IsElementaryTwo (C.map (MulAut.conj g).toMonoidHom) from
        ⟨hn,inferInstance⟩).card_eq_two_pow_rank,hc']
      decide
    exact (intrinsic_sylow_catalogue.2.2 _).mp
      ⟨inferInstance,hcard,hg' ▸ Subgroup.map_mono (hCP.trans hPS)⟩
  exact Subgroup.map_injective (MulAut.conj g).injective
    ((same A hAP hA).trans (same B hBP hB).symm)

end MathieuCode.NormalizedShadowRows.M22CodeQuintet
public noncomputable section
open Sporadic.Mathieu Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.M22CodeFourSpace

/-- An odd-order element fixing the full quintet fixed space is trivial;
the actual pointwise kernel is the elementary quintet two-core. -/
theorem odd_fixed_eq_one (g : MathieuCode.m22PairStabilizer) (ho : Odd (orderOf g))
    (hf : ∀ v ∈ fixedSpace m22OuterCodeRepresentation M22Quintet.K,
      m22OuterCodeRepresentation g v = v) : g = 1 := by
  have hk : g ∈ M22Quintet.K := by
    rw [←pointwise_kernel]
    exact ⟨mem_top _,fun v hv => hf v (le_fixed hv)⟩
  have hp : g^2=1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) g hk
  have hd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hp
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact orderOf_eq_one_iff.mp he
  · rw [he] at ho
    exact (by decide : ¬ Odd 2) ho |>.elim

end MathieuCode.NormalizedShadowRows.M22CodeFourSpace


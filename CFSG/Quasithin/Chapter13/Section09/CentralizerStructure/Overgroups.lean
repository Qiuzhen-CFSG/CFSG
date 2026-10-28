module

public import CFSG.Quasithin.Chapter13.Section09.CentralizerStructure.Pair
public import CFSG.Quasithin.Chapter13.Section09.TerminalObstruction

/-!
# The weak-closure and solvability deductions in 13.9.8

A subgroup weakly closed in T and contained in O₂(C_G(z)) is normal
in C_G(z): every conjugate stays in the two-core, hence in the original T.
This excludes A from that core by 13.9.5 and N_G(A)=M. Once the three
overgroups of Q identify BQ with the two-core, it proves normality of B
and the required containment in K=N_G(B).

The final deduction uses the original Q≤T and its actual centralizer
quotient to discharge the two-group input of the terminal obstruction.
The orthogonal recognition and the identification BQ=O₂(C_G(z)) remain
explicit inputs here; this module does not claim those parts of 13.9.8.

Source: Aschbacher–Smith, proof of 13.9.8, printed p.972 (PDF p.989).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.CentralizerStructure
open Subgroup
variable {G : Type*} [Group G] {d : Configuration G}

/-- The original ambient weak-closure convention from 13.9.2(3). -/
def WeaklyClosed (A : Subgroup G) (T : Sylow 2 G) : Prop :=
  ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
    A.map (MulAut.conj g).toMonoidHom = A

private theorem core_normalized (H : Subgroup G) :
    H ≤ normalizer (H.pCoreIn 2 : Set G) := by
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (pCore 2 H).le_normalizer_map H.subtype

/-- Weak closure becomes normality when all conjugates lie in the normal
two-core of a Sylow overgroup. -/
theorem normalizes_of_weaklyClosed_le_core (A H : Subgroup G)
    (hTH : (d.T : Subgroup G) ≤ H) (hweak : WeaklyClosed A d.T)
    (hA : A ≤ H.pCoreIn 2) : H ≤ normalizer (A : Set G) := by
  have hcoreT : H.pCoreIn 2 ≤ (d.T : Subgroup G) := by
    have hc := pCoreIn_le_sylow H (d.T.subtype hTH)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hc
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply hweak g
  rintro _ ⟨a, ha, rfl⟩
  exact hcoreT ((mem_normalizer_iff.mp (core_normalized H hg) a).mp (hA ha))

namespace PairData
variable (m : PairData d)

/-- The source's exclusion A ⊈ O₂(C_G(z)), using exactly 13.9.2(3–4)
and 13.9.5 and the marked equality C_M(z)=T. -/
theorem A_not_le_core (A : Subgroup G) (hweak : WeaklyClosed A d.T)
    (hNA : normalizer (A : Set G) = d.M)
    (hCM : m.C ⊓ d.M = (d.T : Subgroup G))
    (hgrowth : (d.T : Subgroup G) < m.C) : ¬ A ≤ m.C.pCoreIn 2 := by
  intro hA
  have hCMle : m.C ≤ d.M := hNA ▸
    normalizes_of_weaklyClosed_le_core A m.C m.z_central hweak hA
  have he : m.C = (d.T : Subgroup G) := (inf_eq_left.mpr hCMle).symm.trans hCM
  exact hgrowth.ne he.symm

/-- The final implication of the three-overgroup argument: B is normal
in the literal centralizer, which therefore lies in K=N_G(B). -/
theorem B_normal_of_sup_eq_core (B Q : Subgroup G)
    (hweak : WeaklyClosed B d.T) (hBQ : B ⊔ Q = m.C.pCoreIn 2) :
    (B.subgroupOf m.C).Normal ∧ m.C ≤ normalizer (B : Set G) := by
  have hB : B ≤ m.C.pCoreIn 2 := hBQ ▸ le_sup_left
  have hn := normalizes_of_weaklyClosed_le_core B m.C m.z_central hweak hB
  exact ⟨(normal_subgroupOf_iff_le_normalizer (hB.trans (pCoreIn_le 2 m.C))).mpr hn, hn⟩

variable [Finite G]

/-- Apply the terminal obstruction to the original Q. Its two-group
property follows from Q≤T and is not an additional recognition premise. -/
theorem solvable_of_quotient (Q : Subgroup G) (hQT : Q ≤ (d.T : Subgroup G))
    [hn : (Q.subgroupOf m.C).Normal]
    (e : (m.C ⧸ Q.subgroupOf m.C) ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) : Group.IsSolvable m.C := by
  exact centralizer_solvable_of_twoGroup_quotient m.z (Q.subgroupOf m.C)
    (d.T.isPGroup'.to_le hQT).comap_subtype e

end PairData
end CFSG.Quasithin.Chapter13.Section09.CentralizerStructure

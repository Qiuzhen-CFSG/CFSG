module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.Setup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.ExceptionalFusion.Coordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.ExceptionalFusion.MarkedRealization

/-!
# Exceptional fusion in an odd-prime PSU₃ extension

The explicit quaternion rotation conjugates the field actor c to abc.
The latter lies in the supplied subgroup and inverts its cyclic core.
The scalar marker is fixed by every element of the block image. Thus the
same rotation also handles the second exceptional involution zc, without
changing either the marked involution or the original core.

The already-inverting case uses the identity conjugator. In the remaining
case the marked model realization identifies the original supplied core and
exceptional pair with the hyperbolic model. Thus every supplied cyclic-core
record has exceptional fusion when the odd prime is one modulo four.
The construction of that record remains independent; neither SQTK nor the
supplement condition is needed for its fusion contract.

Source application: Aschbacher--Smith E.1.14(7), printed p.214, citing
Aschbacher (1982), Lemma 4.11; A.3.21(a,b), printed p.55.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
open Matrix.UnitaryQuaternionRotation
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

variable {G : Type*} [Group G] {L T : Subgroup G} {z : G}

/-- The exceptional involution needs no fusion if it already inverts the core. -/
theorem exceptionalFusion_of_inverts (d : CyclicCoreData L T z)
    (hinv : ∀ x ∈ d.core, d.exceptional * x * d.exceptional⁻¹ = x⁻¹) :
    ExceptionalFusion d := by
  refine ⟨1, ?_, ?_, ?_⟩
  · simp
  · simpa using d.exceptional_mem
  · simpa using hinv

/-- The literal quaternion rotation supplies the fusion contract for either
member of the exceptional pair in marked hyperbolic coordinates. -/
theorem exceptionalFusion_of_hyperbolicCoordinates (d : CyclicCoreData L T z)
    {F : Type*} [Field F] {J : HermitianForm 2 F}
    (q : HyperbolicCoordinates d J) : ExceptionalFusion d := by
  let R := rotation J q.form_eq q.r q.i q.r_conj q.i_conj q.i_sq q.two_ne_zero
  let g := q.embedding R
  let a := q.embedding (torus J q.form_eq q.r q.r_conj)
  let b := q.embedding (swap J q.form_eq)
  let s := a * b * q.actor
  have hzT : z ∈ T := d.core_le_sylow d.z_mem
  have haT : a ∈ T := by
    apply d.core_le_sylow
    rw [q.core_eq]
    exact mem_zpowers _
  have hcT : q.actor ∈ T := by
    rcases q.exceptional_pair with he | he
    · rw [← he]
      exact d.exceptional_mem
    · have hc : z⁻¹ * d.exceptional = q.actor := by rw [he]; group
      rw [← hc]
      exact T.mul_mem (T.inv_mem hzT) d.exceptional_mem
  have hsT : s ∈ T := T.mul_mem (T.mul_mem haT q.swap_mem) hcT
  have hgz : MulAut.conj g z = z := by
    have hh := congrArg q.embedding (minusOne_commute J q.form_eq R)
    simp only [map_mul, q.marker_eq] at hh
    change g * z * g⁻¹ = z
    change z * g = g * z at hh
    rw [← hh]
    group
  have hgc : MulAut.conj g q.actor = s :=
    rotation_conjugates_actor J q.form_eq q.r q.i q.r_conj q.i_conj q.i_sq
      q.two_ne_zero q.embedding q.actor q.actor_action
  have hsa : s * a * s⁻¹ = a⁻¹ :=
    twisted_swap_inverts_torus J q.form_eq q.r q.r_conj
      q.embedding q.actor q.actor_action
  have hsx (x : G) (hx : x ∈ d.core) : s * x * s⁻¹ = x⁻¹ := by
    rw [q.core_eq] at hx
    obtain ⟨n, rfl⟩ := hx
    change s * a ^ n * s⁻¹ = (a ^ n)⁻¹
    rw [← conj_zpow, hsa, inv_zpow]
  refine ⟨g, hgz, ?_⟩
  rcases q.exceptional_pair with he | he
  · rw [he, hgc]
    exact ⟨hsT, hsx⟩
  · rw [he, map_mul, hgz, hgc]
    refine ⟨T.mul_mem hzT hsT, ?_⟩
    intro x hx
    let _ := d.cyclic
    let _ := IsCyclic.commGroup (α := d.core)
    have hzxi : z * x⁻¹ = x⁻¹ * z :=
      congrArg Subtype.val (mul_comm (⟨z, d.z_mem⟩ : d.core)
        ⟨x⁻¹, d.core.inv_mem hx⟩)
    calc
      (z * s) * x * (z * s)⁻¹ = z * (s * x * s⁻¹) * z⁻¹ := by group
      _ = z * x⁻¹ * z⁻¹ := by rw [hsx x hx]
      _ = x⁻¹ := by rw [hzxi]; group

/-- Every supplied cyclic core in the odd-prime PSU₃ extension has exceptional
fusion: the conjugator fixes the original marked involution and sends the
original exceptional element to an inverter in the original Sylow subgroup.
All marked-model premises are discharged. -/
theorem exceptionalFusion_of_isPSU [Finite G]
    [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (T : Sylow 2 G) {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (d : CyclicCoreData (generalizedFitting G) (T : Subgroup G) z) :
    ExceptionalFusion d := by
  by_cases hinv : ∀ x ∈ d.core, d.exceptional * x * d.exceptional⁻¹ = x⁻¹
  · exact exceptionalFusion_of_inverts d hinv
  · obtain ⟨F, _, J, ⟨q⟩⟩ :=
      hyperbolicCoordinates_of_isPSU hp ho hmod hmodel T hz hzL hTz d hinv
    exact exceptionalFusion_of_hyperbolicCoordinates d q

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

module
public import Theory.Representation.BinaryAlternatingFiveExtension.Splitting
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelModel
public import Theory.GroupTheory.SplitExtensionCoordinates

/-!
# The Borel two-residual in the original marked natural A₅ extension

The natural kernel splitting theorem supplies a complement in the original
extension. Restricting it to the standard point stabilizer and retaining the
quotient action gives the actual natural A₄ semidirect product. A lift of a
five-point even permutation moves any other prescribed point to the standard
one. Transport of the residual and its two-core then supplies two quaternion
factors generating the original core with central intersection of order two.

The statement retains the original surjection, its kernel coordinates, and
its conjugation formula. No split-extension premise is introduced.

Source: Aschbacher–Smith, the single alternating case of 2.4.29.
-/

public section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup AlternatingFiveBorel
local notation "A5" => alternatingGroup (Fin 5)

private theorem standard_borel_equiv {G : Type*} [Group G] [Finite G]
    (q : G →* A5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e v).toAdd)) :
    Nonempty ((B.comap q) ≃* BorelModel) := by
  obtain ⟨K, hK⟩ := exists_complement q hq e he
  let H := B.comap q
  let f : H →* B :=
    { toFun := fun g => ⟨q g, g.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun g h => Subtype.ext (map_mul q (g : G) (h : G)) }
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := hq b
    exact ⟨⟨g, show q g ∈ B from hg.symm ▸ b.property⟩, Subtype.ext hg⟩
  have hker : f.ker = q.ker.subgroupOf H := by
    ext g
    change (⟨q g, g.property⟩ : B) = 1 ↔ q g = 1
    exact Subtype.ext_iff
  have hle : q.ker ≤ H := by
    intro g hg
    change q g ∈ B
    rw [show q g = 1 from hg]
    exact B.one_mem
  let ek : f.ker ≃* q.ker := (MulEquiv.subgroupCongr hker).trans (subgroupOfEquivOfLe hle)
  have hKB : f.ker.IsComplement' (K.subgroupOf H) :=
    hker.symm ▸ hK.subgroupOf_overgroup hle
  apply exists_semidirect_equiv_of_split_coordinates f.ker (K.subgroupOf H) hKB
    (QuotientGroup.quotientKerEquivOfSurjective f hf) (ek.trans e) borelAction
  intro g u
  change e (ek (MulAut.conjNormal g u)) =
    Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e (ek u)).toAdd)
  have hh : ek (MulAut.conjNormal g u) = MulAut.conjNormal (g : G) (ek u) := by
    apply Subtype.ext
    rfl
  rw [hh]
  exact he g (ek u)

private def mover : Fin 5 → A5 := ![
  ⟨Equiv.swap 0 4 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
  ⟨Equiv.swap 1 4 * Equiv.swap 0 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
  ⟨Equiv.swap 2 4 * Equiv.swap 0 1, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩,
  ⟨Equiv.swap 3 4 * Equiv.swap 0 1, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩, 1]
private theorem mover_apply : ∀ i : Fin 5, (mover i).val i = 4 := by decide +kernel

/-- The actual inverse image of any A₅ point stabilizer has the natural A₄ extension model. -/
theorem borel_equiv {G : Type*} [Group G] [Finite G]
    (q : G →* A5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e v).toAdd))
    (i : Fin 5) : Nonempty (((MulAction.stabilizer A5 i).comap q) ≃* BorelModel) := by
  obtain ⟨eb⟩ := standard_borel_equiv q hq e he
  obtain ⟨g, hg⟩ := hq (mover i)
  let J := (MulAction.stabilizer A5 i).comap q
  have hinv : (mover i).val⁻¹ 4 = i := (mover i).val.symm_apply_eq.mpr (mover_apply i).symm
  have hc (x : G) : MulAut.conj g x ∈ B.comap q ↔ x ∈ J := by
    change (q (g * x * g⁻¹)).val 4 = 4 ↔ (q x).val i = i
    rw [map_mul, map_mul, map_inv, hg]
    change (mover i).val ((q x).val ((mover i).val⁻¹ 4)) = 4 ↔ (q x).val i = i
    rw [hinv, ← mover_apply i]
    exact (mover i).val.injective.eq_iff
  have hm : J.map (MulAut.conj g).toMonoidHom = B.comap q := by
    ext y
    rw [mem_map_equiv]
    rw [← hc ((MulAut.conj g).symm y), MulEquiv.apply_symm_apply]
  exact ⟨((MulAut.conj g).subgroupMap J).trans ((MulEquiv.subgroupCongr hm).trans eb)⟩

/-- In the original marked A₅ extension, the two-core of the point-Borel two-residual
is the central product of two quaternion groups of order eight. -/
theorem borel_residual_quaternion {G : Type*} [Group G] [Finite G]
    (q : G →* A5) (hq : Function.Surjective q) (e : q.ker ≃* V)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 5) (q g).val (e v).toAdd))
    (i : Fin 5) : Nonempty (QuaternionCentralProductData
      (pCore 2 (pResidual 2 ((MulAction.stabilizer A5 i).comap q)))) := by
  obtain ⟨eb⟩ := borel_equiv q hq e he i
  let er := (eb.subgroupMap (pResidual 2 ((MulAction.stabilizer A5 i).comap q))).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 eb.toMonoidHom eb.surjective))
  let ep := (er.subgroupMap (pCore 2 (pResidual 2 ((MulAction.stabilizer A5 i).comap q)))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 er))
  exact ⟨borelCoreQuaternionData.map ep.symm⟩
end BinaryPermutation.AlternatingFiveExtension

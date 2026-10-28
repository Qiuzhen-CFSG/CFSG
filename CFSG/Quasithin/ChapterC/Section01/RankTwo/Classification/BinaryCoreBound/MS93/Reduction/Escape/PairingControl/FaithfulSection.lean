module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Basic

/-!
# Faithfulness at the end of MS93 (4.3.2)

If an actor in the vertex stabilizer centralizes Vcirc modulo Z, it lies in
Q. This follows from the actual natural section supplied by (4.3.1)(iii).
In its notation D = Z[V,Q]. The generation G = Ltilde Q identifies the
moving preimage with D[V,Ltilde]. The actor therefore centralizes this
moving group modulo D, so its matrix fixes each vector of the natural
three-space. The coordinate marking is faithful and has kernel exactly Q.

The argument retains both intrinsic quotient kernels and works with the
actual conjugation equation, rather than a natural-module label. It is the
final step after the last (1.7)(ii) application supplies the commutator bound;
that application remains a separate obligation.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.881,883,885--886.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl

private theorem naturalFactor_actor_le_kernel {A : Type*} [Group A]
    {π : A →* SL} {L H N W : Subgroup A}
    (n : RankOnePairing.NaturalFactor π L H N) (hW : W ≤ L)
    (hc : ⁅H, W⁆ ≤ N) : W ≤ π.ker := by
  intro w hw
  have hf (x : H) :
      (n.marking (π w)).val.mulVec (Multiplicative.toAdd (n.coordinates x)) =
        Multiplicative.toAdd (n.coordinates x) := by
    let y : H := ⟨w * (x : A) * w⁻¹,
      (mem_normalizer_iff.mp (n.normalized (hW hw)) _).mp x.property⟩
    have hy : n.coordinates y = n.coordinates x := by
      have hk : y * x⁻¹ ∈ n.coordinates.ker := by
        rw [n.kernel]
        change w * (x : A) * w⁻¹ * (x : A)⁻¹ ∈ N
        exact (commutator_comm H W ▸ hc) (commutator_mem_commutator hw x.property)
      simpa only [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] using hk
    rw [← n.action w (hW hw) x y rfl, hy]
  have hm : n.marking (π w) = 1 := by
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    obtain ⟨x, hx⟩ := n.surjective (Multiplicative.ofAdd (Pi.single j 1))
    have hh := congrFun (hf x) i
    rw [hx] at hh
    change (n.marking (π w)).val.mulVec (Pi.single j 1) i =
      (Pi.single j 1 : Fin 3 → ZMod 2) i at hh
    simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using hh
  exact n.marking.map_eq_one_iff.mp hm

private theorem movingPreimage_eq_of_generation {A : Type*} [Group A]
    {π : A →* SL} {Q L H N : Subgroup A} [L.Normal]
    (s : SingleNaturalSection π Q L H N) (hgen : L ⊔ Q = ⊤) :
    movingPreimage Q H N = radicalPreimage Q H N ⊔ ⁅H, L⁆ := by
  let := s.normal_group
  let := s.radical_normal
  let D := radicalPreimage Q H N ⊔ ⁅H, L⁆
  have htop : (⊤ : Subgroup A) ≤ commutatorPreimage ⊤ H D := by
    apply hgen.ge.trans
    apply sup_le
    · apply le_commutatorPreimage (Q := ⊤) (E := H) (Z := D) (D := L) le_top
      rw [commutator_comm]
      exact le_sup_right
    · apply le_commutatorPreimage (Q := ⊤) (E := H) (Z := D) (D := Q) le_top
      rw [commutator_comm]
      exact le_sup_right.trans le_sup_left
  apply le_antisymm
  · apply sup_le le_sup_left
    rw [commutator_comm]
    exact (commutator_mono htop le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ H D le_normalizer_of_normal)
  · exact sup_le le_sup_left ((commutator_mono le_rfl le_top).trans le_sup_right)

private theorem singleNaturalSection_actor_le_Q {A : Type*} [Group A]
    {π : A →* SL} {Q L H N W : Subgroup A} [L.Normal]
    (s : SingleNaturalSection π Q L H N) (hgen : L ⊔ Q = ⊤)
    (hc : ⁅⁅H, L⁆, W⁆ ≤ N) : W ≤ Q := by
  let := s.radical_normal
  have hpre : movingPreimage Q H N ≤
      commutatorPreimage ⊤ W (radicalPreimage Q H N) := by
    rw [movingPreimage_eq_of_generation s hgen]
    apply sup_le
    · exact le_commutatorPreimage le_top (commutator_le_left _ _)
    · exact le_commutatorPreimage le_top (hc.trans le_sup_left)
  rw [← s.projection_kernel]
  apply naturalFactor_actor_le_kernel s.natural le_top
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le ⊤ W (radicalPreimage Q H N) le_normalizer_of_normal)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

theorem actor_le_Q (source : LocalSource L R) {a : Vertex R} (ha : color R a = false)
    (s : NaturalSectionAt a (V R a) (Z R a))
    (W : Subgroup (FreeAmalgam R)) (hW : W ≤ stabilizer R a)
    (hc : ⁅Vcirc R a, W⁆ ≤ Z R a) : W ≤ Q R a := by
  let S := stabilizer R a
  have hgen : pResidual 2 S ⊔ (Q R a).subgroupOf S = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      ← MonoidHom.range_eq_map, range_subtype]
    exact source.local_generation a ha
  have hnative : ⁅⁅(V R a).subgroupOf S, pResidual 2 S⁆, W.subgroupOf S⁆ ≤
      (Z R a).subgroupOf S := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le s.local_group,
      map_subgroupOf_eq_of_le hW]
    exact hc
  have hbound := singleNaturalSection_actor_le_Q s.module_section hgen hnative
  intro w hw
  exact hbound (show (⟨w, hW hw⟩ : S) ∈ W.subgroupOf S from hw)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl

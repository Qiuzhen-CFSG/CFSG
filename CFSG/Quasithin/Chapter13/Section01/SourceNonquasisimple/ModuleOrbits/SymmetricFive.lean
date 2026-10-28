module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Frattini
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerOrbits.SymmetricFive.Source

/-!
# The marked symmetric-five branch on the original moved subgroup

This is the orbit consumer of 13.1.10(2), not a construction of that marking.
The acting group is the literal LT=L∨T. A local Sylow representative in
C_M(u) remains local Sylow in C_LT(u), so the proved deleted-permutation
orbit calculation gives [T:C_T(u)]≤2. For a vector moved by T it also
identifies the actual component-centralizer image as S₃. Equivariance
transfers its noncommutativity to the original action on U, and the kernel
comparison transfers it to the original odd Frattini action.

The module marking, with its maps and equivariance, is the sole input from
the pending 13.1.10 classification. No orbit or stabilizer fact is assumed.
Source: Aschbacher--Smith, 13.1.10(2), 13.1.12(1--2), pp.871--873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits
open Chapter1 Chapter1.Section02 Chapter12.Section02
open SourceCentralizerOrbits.SymmetricFive
variable {G : Type*} [Group G] [Finite G]

/-- A genuine deleted-permutation marking of the source LT-action on U.
The image of the original L is the actual alternating subgroup. -/
structure SymmetricFiveMarking (T : Sylow 2 G) (L : Subgroup G) where
  invariant : L ⊔ (T : Subgroup G) ≤ normalizer (normalizerMoved L : Set G)
  quotient : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 5)
  surjective : Function.Surjective quotient
  coordinates : normalizerMoved L ≃* Multiplicative (natural (Fin 5))
  equivariant : ∀ (m : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : normalizerMoved L),
    coordinates ((normalizerMoved L).normalizerMonoidHom (inclusion invariant m) v) =
      naturalMulAction (Fin 5) (quotient m) (coordinates v)
  component : (L.subgroupOf (L ⊔ (T : Subgroup G))).map quotient = alternatingGroup (Fin 5)

namespace SymmetricFiveMarking
variable {T : Sylow 2 G} {L : Subgroup G} (d : SymmetricFiveMarking T L)
include d

omit [Finite G] in
/-- The model homomorphism on L has exactly the actual moved-action kernel. -/
theorem component_kernel :
    (d.quotient.comp (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))).ker =
      (componentAction L).ker := by
  ext l
  rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
  have he (v : normalizerMoved L) :
      d.coordinates (componentAction L l v) =
        naturalMulAction (Fin 5) (d.quotient (inclusion le_sup_left l)) (d.coordinates v) :=
    d.equivariant (inclusion le_sup_left l) v
  constructor
  · intro hl
    apply MulEquiv.ext
    intro v
    apply d.coordinates.injective
    rw [he]
    change naturalMulAction (Fin 5)
      ((d.quotient.comp (inclusion le_sup_left)) l) (d.coordinates v) = d.coordinates v
    rw [hl,map_one]
    rfl
  · intro hl
    apply naturalMulAction_injective_of_odd (Fin 5) (by decide)
    rw [map_one]
    apply MulEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := d.coordinates.surjective w
    change naturalMulAction (Fin 5) (d.quotient (inclusion le_sup_left l)) (d.coordinates v) = _
    rw [← he,hl]
    rfl

/-- The source marking uses exactly L/O∞(L), with no extra kernel premise. -/
theorem component_kernel_eq_radical
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (d.quotient.comp (inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left))).ker =
      solvableRadical L := by
  rw [d.component_kernel,componentAction_ker_eq_radical h hmany hL hn]

omit [Finite G] in
/-- A nonabelian marked centralizer image implies a nonabelian original image. -/
theorem moved_centralizer_not_commutative (u : G)
    (hnc : ¬ IsMulCommutative
      (((L ⊓ centralizer ({u} : Set G)).subgroupOf (L ⊔ (T : Subgroup G))).map d.quotient)) :
    ¬ IsMulCommutative (((centralizer ({u} : Set G)).subgroupOf L).map (componentAction L)) := by
  intro hc
  apply hnc
  apply isMulCommutative_iff.mpr
  intro a b
  obtain ⟨l,hl,hel⟩ := a.property
  obtain ⟨k,hk,hek⟩ := b.property
  let lL : L := ⟨l,hl.1⟩
  let kL : L := ⟨k,hk.1⟩
  let A := ((centralizer ({u} : Set G)).subgroupOf L).map (componentAction L)
  let lA : A := ⟨componentAction L lL,⟨lL,hl.2,rfl⟩⟩
  let kA : A := ⟨componentAction L kL,⟨kL,hk.2,rfl⟩⟩
  have hh := congrArg Subtype.val ((isMulCommutative_iff.mp hc) lA kA)
  change componentAction L lL * componentAction L kL =
    componentAction L kL * componentAction L lL at hh
  have he (x : (L ⊔ (T : Subgroup G) : Subgroup G)) (hx : (x : G) ∈ L)
      (v : normalizerMoved L) :
      d.coordinates (componentAction L ⟨x,hx⟩ v) =
        naturalMulAction (Fin 5) (d.quotient x) (d.coordinates v) := d.equivariant x v
  apply Subtype.ext
  change (a : Equiv.Perm (Fin 5))*(b : Equiv.Perm (Fin 5)) =
    (b : Equiv.Perm (Fin 5))*(a : Equiv.Perm (Fin 5))
  rw [← hel,← hek]
  apply naturalMulAction_injective_of_odd (Fin 5) (by decide)
  rw [map_mul,map_mul]
  apply MulEquiv.ext
  intro w
  obtain ⟨v,rfl⟩ := d.coordinates.surjective w
  have hv := congrArg (fun f : MulAut (normalizerMoved L) => d.coordinates (f v)) hh
  change d.coordinates (componentAction L lL (componentAction L kL v)) =
    d.coordinates (componentAction L kL (componentAction L lL v)) at hv
  change naturalMulAction (Fin 5) (d.quotient l)
      (naturalMulAction (Fin 5) (d.quotient k) (d.coordinates v)) =
    naturalMulAction (Fin 5) (d.quotient k)
      (naturalMulAction (Fin 5) (d.quotient l) (d.coordinates v))
  calc
    _ = d.coordinates (componentAction L lL (componentAction L kL v)) := by
      rw [he l hl.1 (componentAction L kL v),he k hk.1 v]
    _ = d.coordinates (componentAction L kL (componentAction L lL v)) := hv
    _ = _ := by rw [he k hk.1 (componentAction L lL v),he l hl.1 v]

/-- For the locally Sylow representative, the literal index is at most two;
the non-2-central branch has the specified S₃ component image. -/
theorem centralizer_orbit
    (h : Hypothesis1311 T) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (u : normalizerMoved L) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 ∧
      (¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G) →
        Nonempty ((((L ⊓ centralizer ({(u : G)} : Set G)).subgroupOf
          (L ⊔ (T : Subgroup G))).map d.quotient) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ IsMulCommutative (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
          (componentAction L))) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hT : IsSylowIn 2 (T : Subgroup G) (L ⊔ (T : Subgroup G)) := by
    apply isSylowIn_iff.mpr
    exact ⟨T.isPGroup',le_sup_right,fun A hA hTA _ => T.is_maximal' hA hTA⟩
  have hlocal' := hlocal.restrict
    (inf_le_inf_right (centralizer ({(u : G)} : Set G)) le_sup_right)
    (inf_le_inf_right (centralizer ({(u : G)} : Set G)) (sup_le L.le_normalizer hTL))
  obtain ⟨hi,hs⟩ := source_symmetricFive_natural_orbit_and_stabilizer
    (L ⊔ (T : Subgroup G)) (normalizerMoved L) d.invariant d.quotient d.surjective
    d.coordinates d.equivariant (T : Subgroup G) L hT d.component u hu hlocal'
  exact ⟨hi,fun hm => ⟨(hs hm).1,d.moved_centralizer_not_commutative u (hs hm).2⟩⟩

/-- The selected S₅ branch supplies the index and noncommutativity on the
literal odd Frattini quotient used by the centralizer sieve. -/
theorem centralizer_index_and_frattini_image
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L) (hu : u ≠ 1)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 ∧
      (¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G) →
        ¬ IsMulCommutative (xiFrattiniAction
          (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)) (XiP p L)
          (XiP_invariant p inf_le_left)).range) := by
  obtain ⟨hi,hs⟩ := d.centralizer_orbit h hL hn u hu hlocal
  exact ⟨hi,fun hm => centralizer_frattini_image_not_commutative h hmany hL hn ho hd u
    (hs hm).2⟩

end SymmetricFiveMarking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits

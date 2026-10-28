module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.Basic
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank
public import Theory.Representation.BinaryPlaneInvolutionFixed


/-!
# The order-two center of H/U in J.4.1(4)

The original H/Q map descends to H/U. Since S₅ has trivial center, the
center of H/U lies in Q/U. The original Ru2 coordinate map then identifies
it with the vectors fixed by the entire six-dimensional S₅ action.
Every fixed vector lies in HC/U, the two-dimensional kernel of the natural
head. A₅ fixes this plane, while indecomposability makes an odd involution
act nontrivially. Its fixed space is therefore a binary line. The proof
uses the earlier proved kernel-movement theorem and retains both literal
quotient maps; it assumes no center or module-identification conclusion.

Source: Aschbacher–Smith J.4.1(4), printed p.440 (PDF p.451).
-/

public section
noncomputable section

open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

@[expose] def hatStar : Hat d →* S5 := QuotientGroup.lift _ d.ru2.quotientMap (by
  intro h hh
  rw [d.ru2.quotient_kernel]
  exact d.ru2.six.kernel_le hh)

theorem hatStar_apply (h : d.toTypeRuSetup.H) :
    hatStar d (hatMap d h) = d.ru2.quotientMap h := rfl

theorem hatStar_surjective : Function.Surjective (hatStar d) :=
  QuotientGroup.lift_surjective_of_surjective _ _ d.ru2.quotient_surjective _

theorem hatStar_kernel : (hatStar d).ker = hat d d.toTypeRuSetup.Q := by
  rw [hatStar,QuotientGroup.ker_lift,d.ru2.quotient_kernel]
  rfl

theorem center_le_hat_Q : center (Hat d) ≤ hat d d.toTypeRuSetup.Q := by
  rw [← hatStar_kernel]
  intro x hx
  change hatStar d x = 1
  have hz : hatStar d x ∈ center S5 := by
    rw [mem_center_iff]
    intro g
    obtain ⟨h,rfl⟩ := hatStar_surjective d g
    rw [← map_mul,← map_mul,mem_center_iff.mp hx h]
  rwa [Theory.SpecificGroups.SymmetricFive.center_eq_bot,mem_bot] at hz

def sixToHat : Multiplicative SixSpace →* Hat d :=
  d.ru2.six.coordinates.liftOfSurjective d.ru2.six.onto
    ⟨(hatMap d).comp (inclusion (pCoreIn_le 2 _)),by
      intro q hq
      exact (hatMap_eq_one d _).mpr ((d.ru2.six.coordinates_eq_one_iff q).mp hq)⟩

theorem sixToHat_coordinates (q : d.toTypeRuSetup.Q) :
    sixToHat d (d.ru2.six.coordinates q) = hatMap d (inclusion (pCoreIn_le 2 _) q) :=
  d.ru2.six.coordinates.liftOfRightInverse_comp_apply _ _ _ q

theorem sixToHat_injective : Function.Injective (sixToHat d) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨q,rfl⟩ := d.ru2.six.onto x
  rw [MonoidHom.mem_ker,sixToHat_coordinates,hatMap_eq_one] at hx
  exact (d.ru2.six.coordinates_eq_one_iff q).mpr hx

theorem sixToHat_range : (sixToHat d).range = hat d d.toTypeRuSetup.Q := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    obtain ⟨q,rfl⟩ := d.ru2.six.onto v
    rw [sixToHat_coordinates]
    exact mem_map.mpr ⟨inclusion (pCoreIn_le 2 _) q,q.property,rfl⟩
  · rintro ⟨h,hh,rfl⟩
    exact ⟨d.ru2.six.coordinates ⟨h,hh⟩,sixToHat_coordinates d ⟨h,hh⟩⟩

theorem sixToHat_mem_center_iff (v : SixSpace) :
    sixToHat d (Multiplicative.ofAdd v) ∈ center (Hat d) ↔
      ∀ g : S5, d.ru2.sixAction g v = v := by
  obtain ⟨q,hq⟩ := d.ru2.six.onto (Multiplicative.ofAdd v)
  have hv : (d.ru2.six.coordinates q).toAdd = v := congrArg Multiplicative.toAdd hq
  rw [← hq,sixToHat_coordinates]
  constructor
  · intro hc g
    obtain ⟨h,rfl⟩ := d.ru2.quotient_surjective g
    have hm : ⁅(h:G),(q:G)⁆ ∈ d.toTypeRuSetup.U := by
      apply (hatMap_eq_one d ⁅h,inclusion (pCoreIn_le 2 _) q⁆).mp
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact mem_center_iff.mp hc (hatMap d h)
    have he := (Fusion.Outer.six_commutator_mem_U_iff d h q).mp hm
    rwa [hv] at he
  · intro hf
    apply mem_center_iff.mpr
    intro x
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H) x
    change hatMap d h * hatMap d (inclusion (pCoreIn_le 2 _) q) =
      hatMap d (inclusion (pCoreIn_le 2 _) q) * hatMap d h
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    apply (hatMap_eq_one d _).mpr
    apply (Fusion.Outer.six_commutator_mem_U_iff d h q).mpr
    rw [hv]
    exact hf _

open Representation.OneCohomology Fusion.Outer

theorem card_center_eq_fixed : Nat.card (center (Hat d)) = Nat.card (fixed d.ru2.sixAction) := by
  let f : fixed d.ru2.sixAction → center (Hat d) := fun v =>
    ⟨sixToHat d (Multiplicative.ofAdd v.val),(sixToHat_mem_center_iff d v.val).mpr v.property⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact Multiplicative.ofAdd.injective (sixToHat_injective d (congrArg Subtype.val he))
  have hs : Function.Surjective f := by
    intro z
    have hz := center_le_hat_Q d z.property
    rw [← sixToHat_range] at hz
    obtain ⟨w,hw⟩ := hz
    have hfix : ∀ g:S5, d.ru2.sixAction g w.toAdd = w.toAdd :=
      (sixToHat_mem_center_iff d w.toAdd).mp (hw.symm ▸ z.property)
    exact ⟨⟨w.toAdd,hfix⟩,Subtype.ext hw⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)).symm

private theorem fixed_vector_of_alternating_and_outer
    {ρ : Representation (ZMod 2) S5 SixSpace} {v : SixSpace}
    (hA : ∀ a:alternatingGroup (Fin 5),ρ a v = v)
    (t:S5) (ht:t ∉ alternatingGroup (Fin 5)) (hfix:ρ t v=v) :
    ∀ g:S5,ρ g v=v := by
  have hts : t.sign = -1 := (Int.units_eq_one_or _).resolve_left
    (fun h => ht (Equiv.Perm.mem_alternatingGroup.mpr h))
  intro g
  by_cases hg:g ∈ alternatingGroup (Fin 5)
  · exact hA ⟨g,hg⟩
  have hgs : g.sign = -1 := (Int.units_eq_one_or _).resolve_left
    (fun h => hg (Equiv.Perm.mem_alternatingGroup.mpr h))
  have hgt : g*t⁻¹ ∈ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_inv,hgs,hts]
    simp
  calc
    ρ g v = ρ (g*t⁻¹) (ρ t v) := by
      rw [← Module.End.mul_apply,← map_mul]
      simp
    _ = ρ (g*t⁻¹) v := by rw [hfix]
    _ = v := hA ⟨g*t⁻¹,hgt⟩

/-- The actual six-space has a single binary line fixed by the entire S₅ action. -/
theorem six_fixed_card : Nat.card (fixed d.ru2.sixAction) = 2 := by
  let head := d.fusionNaturalHead
  let p := head.sixProjection d
  let ρ := head.kernelAction d
  let t:S5 := Equiv.swap 0 1
  have ht : t ∉ alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    change (Equiv.swap (0:Fin 5) 1).sign ≠ 1
    decide +kernel
  have ht2 : t*t=1 := by decide +kernel
  have hfixed : ∀ q∈d.toTypeRuSetup.HC,∀ k∈d.toTypeRuSetup.K,
      ⁅k,q⁆ ∈ d.toTypeRuSetup.U :=
    fun q hq k hk => d.HC_commutator_K_mem_U ⟨q,hq⟩ ⟨k,hk⟩
  have hm := head.sixProjection_kernel_moved d hfixed t ht ht2
  have hc : Nat.card (ρ t - 1).ker = 2 := by
    apply BinaryInvolution.fixed_card_of_finrank_two ρ t ht2
      (head.finrank_sixProjection_kernel d)
    obtain ⟨v,hv,hn⟩ := hm
    exact ⟨⟨v,hv⟩,fun he => hn (congrArg Subtype.val he)⟩
  have hA (a:alternatingGroup (Fin 5)) (v:SixSpace) (hv:v∈p.ker) :
      d.ru2.sixAction a v=v := head.sixProjection_kernel_fixed d hfixed a v hv
  have hker (v:fixed d.ru2.sixAction) : (v:SixSpace) ∈ p.ker := by
    apply SL2FourNatural.natural_fixed_eq_zero
    intro a
    rw [← head.action.restriction,← head.sixProjection_equivariant]
    rw [v.property]
  let f : (ρ t-1).ker → fixed d.ru2.sixAction := fun v =>
    ⟨v.val.val,fixed_vector_of_alternating_and_outer
      (fun a => hA a v.val.val v.val.property) t ht
      (congrArg Subtype.val (sub_eq_zero.mp v.property))⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : fixed d.ru2.sixAction => z.val) he
  have hs : Function.Surjective f := by
    intro v
    have hmem : (⟨v.val,hker v⟩ : p.ker) ∈ (ρ t-1).ker := by
      change ρ t ⟨v.val,hker v⟩ - ⟨v.val,hker v⟩ = 0
      apply sub_eq_zero.mpr
      exact Subtype.ext (v.property t)
    exact ⟨⟨⟨v.val,hker v⟩,hmem⟩,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)).symm.trans hc

/-- J.4.1(4), with the original literal quotient H/U. -/
theorem center_hat_card : Nat.card (center (Hat d)) = 2 :=
  (card_center_eq_fixed d).trans (six_fixed_card d)

end CFSG.Quasithin.ChapterJ.RuSubgroup

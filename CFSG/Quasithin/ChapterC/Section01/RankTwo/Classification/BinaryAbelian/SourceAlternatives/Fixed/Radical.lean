module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Fixed.RadicalImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.SourceAlternatives.Fixed.Point
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalPoint
public import Theory.SpecificGroups.PSL3Two.Parabolics.OddIndex
public import Theory.Representation.SLThreeCentralExtension.Involutions

/-!
# The radical in the fixed-line binary MS alternative

Odd-index radicality and a fixed vector outside the kernel of the actual
four-dimensional cover force an elementary radical of order four: a
Sylow radical would split the cover, and the other odd-index subgroups
are the two parabolics. Every involution fixing the lifted vector has it
in its displacement space. Its nonzero projection therefore determines
the transvection center, placing the involution in the point radical.
Equality follows from the two orders four. That radical has a unique
nonzero natural fixed vector, so any point fixed by it gives the same
parabolic. The final application pulls this equality back along the
original ambient actor, whose kernel is O₂(J).

Source: Aschbacher–Smith C.1.34(5), printed p.137;
Meierfrankenfeld–Stellmacher, “Pushing up weak BN-pairs of rank two”
(1993), Main Theorem (8), printed p.830.
-/

public section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS

namespace FixedCover
open BinaryLinearThree
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) BinaryLinearThree.Group V)
  (p : ρ.IntertwiningMap W) (hp : IsCover p)
  (hd : Module.finrank (ZMod 2) V = 4)
  (T : Subgroup BinaryLinearThree.Group) (hT : MSOddIndexRadical T)
  (x : V) (hx : p x ≠ 0) (hf : ∀ t ∈ T, ρ t x = x)

include ρ p hp hd T hT x hx hf

private theorem radical_data : IsElementaryAbelian 2 T ∧ Nat.card T = 4 := by
  obtain ⟨H,hH,hodd,hcore⟩ := hT
  change H.pCoreIn 2 = T at hcore
  have htwo : ¬ IsPGroup 2 H := by
    intro htwo
    have he : H = T := (pCoreIn_eq_self_of_isPGroup 2 H htwo).symm.trans hcore
    let S : Sylow 2 BinaryLinearThree.Group := htwo.toSylow hodd.not_two_dvd_nat
    have hbij := SLThreeCentralExtension.cover_bijective_of_sylow_fixed ρ p hp S x hx
      (fun t ht => hf t (he.le ht))
    have heq := (LinearEquiv.ofBijective p.toLinearMap hbij).finrank_eq
    have hW : Module.finrank (ZMod 2) Vector = 3 := Module.finrank_fin_fun (ZMod 2)
    rw [hd,hW] at heq
    omega
  rw [← hcore]
  exact Matrix.PSL3Two.odd_index_core_data H hH.ne hodd htwo

/-- The radical is exactly the ambient two-core of every nonzero natural
point that it fixes. The lifted fixed point belongs to the nonsplit cover. -/
theorem naturalPoint_core_eq (v : Vector) (hv : v ≠ 0)
    (hvT : ∀ t ∈ T, W t v = v) : (naturalPoint v).pCoreIn 2 = T := by
  have hdata := radical_data ρ p hp hd T hT x hx hf
  let := hdata.1
  have hle : T ≤ (naturalPoint (p x)).pCoreIn 2 := by
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]
      exact one_mem _
    have ho : orderOf t = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) t ht) ht1
    have hr := BinaryLinearThree.NaturalExtension.involution_range_eq_fixed ρ hd t ho
      (BinaryLinearThree.NaturalExtension.involution_codim_of_commutator_top ρ hd hp.2.2 t ho)
    have hxf : x ∈ BinaryOffender.fixedSpace ρ (zpowers t) :=
      (BinaryOffender.mem_fixedSpace_zpowers_iff ρ t x).mpr (hf t ht)
    rw [← hr.1] at hxf
    obtain ⟨y,hy⟩ := hxf
    have he : W t (p y) - p y = p x := by
      have hh := congrArg p hy
      change p (ρ t y - y) = p x at hh
      simpa only [map_sub,p.isIntertwining] using hh
    exact involution_mem_naturalPoint_core t ho (p x) hx (p y) he
  have heq : T = (naturalPoint (p x)).pCoreIn 2 :=
    eq_of_le_of_card_ge hle (by rw [hdata.2,card_naturalPoint_core _ hx])
  have hvx : v = p x := naturalPoint_core_fixed_unique (p x) v hx hv (by
    rw [← heq]
    exact hvT)
  rw [hvx,← heq]

end FixedCover

universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R) [IsElementaryAbelian 2 (commutatorCore L)]
namespace AbelianCore.NaturalQuotient
variable (q : NaturalQuotient h 1)

/-- The point subgroup is the literal preimage under the ambient actor. -/
theorem pointSubgroup_eq_comap (v : BinaryLinearThree.Vector) :
    q.pointSubgroup h v = (BinaryLinearThree.naturalPoint v).comap (q.ambientActor h) := by
  ext j
  rfl

/-- The actual C.1.34(5) point subgroup has radical R, for any group class κ.
The original Sylow containment supplies the required fixed natural point. -/
theorem pointSubgroup_pCoreIn (hd : Nat.card (commutatorCore L) = 16)
    (S : Sylow 2 J) (hRS : R ≤ (S : Subgroup J))
    (v : BinaryLinearThree.Vector) (hv : v ≠ 0)
    (hSv : (S : Subgroup J) ≤ q.pointSubgroup h v) :
    (q.pointSubgroup h v).pCoreIn 2 = R := by
  have hdim : Module.finrank (ZMod 2) (Additive (commutatorCore L)) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (commutatorCore L))
    rw [Nat.card_zmod] at hh
    change Nat.card (commutatorCore L) = _ at hh
    rw [hd] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) (hh.symm.trans (by decide : 16 = 2^4))
  obtain ⟨d,hdC,hdfix⟩ := q.exists_radical_fixed_core h hd
  have hnonzero : q.oneProjection h (Additive.ofMul d) ≠ 0 :=
    fun he => hdC ((q.oneProjection_kernel h _).mp he)
  have hfix : ∀ t ∈ R.map (q.ambientActor h),
      q.oneRepresentation h t (Additive.ofMul d) = Additive.ofMul d := by
    rintro t ⟨r,hr,rfl⟩
    change Additive.ofMul (q.action h inferInstance (q.ambientActor h r) d) = _
    rw [q.ambientActor_action,hdfix r hr]
  have himage := FixedCover.naturalPoint_core_eq (q.oneRepresentation h) (q.oneProjection h)
    (q.oneProjection_isCover h) hdim (R.map (q.ambientActor h)) (q.ambient_radical_image h)
    (Additive.ofMul d) hnonzero hfix v hv (by
      rintro t ⟨r,hr,rfl⟩
      exact hSv (hRS hr))
  have hker : IsPGroup 2 (q.ambientActor h).ker := by
    rw [q.ambientActor_kernel]
    exact pCore_isPGroup
  have hkR : (q.ambientActor h).ker ≤ R := by
    rw [q.ambientActor_kernel]
    exact h.radical.twoCore_le
  have hkP : (q.ambientActor h).ker ≤ (q.pointSubgroup h v).pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes hker
    · rw [q.pointSubgroup_eq_comap]
      exact ker_le_comap _ _
    · rw [(q.ambientActor h).ker.normalizer_eq_top]
      exact le_top
  apply map_injective_of_ker_le (q.ambientActor h) hkP hkR
  rw [map_pCoreIn_of_ker_isPGroup (q.ambientActor h) hker,
    q.pointSubgroup_eq_comap,map_comap_eq_self_of_surjective (q.ambientActor_surjective h),himage]

end AbelianCore.NaturalQuotient
end CFSG.Quasithin.ChapterC.BinaryMS

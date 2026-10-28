module
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.RankTwoSectionNineSplit
public import Theory.GroupTheory.NormalSymmetricThreePairRank.TwoPerfect
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual

/-!
# Normal symmetric-three pairs in rank-two sections

A normal S₃ × S₃ in a quotient of a finite group of three-rank at most two
has a three-free centralizer. A cubic in that centralizer would form a
noncyclic three-subgroup centralizing one S₃ coordinate, contradicting
A.1.31 applied to the original cover. Consequently every two-perfect
{2,3}-subgroup lies in the pair. It is subnormal there because the pair's
two-residual is abelian of order nine.

The rank hypothesis stays on the source of the displayed surjection.
No arbitrary quotient-rank monotonicity is used. The application is the
doubled S₃ exclusion in Aschbacher–Smith 14.7.32, printed p.1059.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.NormalSymmetricThreePairRank
local notation "S3" => Equiv.Perm (Fin 3)
variable {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]

/-- A symmetric-three pair in a rank-two section has three-free centralizer,
with rank retained on the original source of the displayed surjection. -/
theorem three_not_dvd_card_centralizer_of_cover
    (q : D →* Q) (hq : Function.Surjective q) (hr : primeRank 3 D ≤ 2)
    (K : Subgroup Q) (e : K ≃* S3 × S3) :
    ¬ 3 ∣ Nat.card (centralizer (K : Set Q)) := by
  intro hd
  let C := centralizer (K : Set Q)
  obtain ⟨c,hc⟩ := exists_prime_orderOf_dvd_card' 3 hd
  let B : Subgroup S3 := zpowers (Equiv.swap 0 1 * Equiv.swap 1 2)
  have hB : Nat.card B = 3 := by
    rw [show B = zpowers (Equiv.swap 0 1 * Equiv.swap 1 2) from rfl,Nat.card_zpowers]
    apply orderOf_eq_prime (p := 3) <;> decide
  let P := zpowers c
  have hP : Nat.card P = 3 := (Nat.card_zpowers c).trans hc
  let k := K.subtype.comp e.symm.toMonoidHom
  let j := k.comp (MonoidHom.inl S3 S3)
  have hj : Function.Injective j := K.subtype_injective.comp (e.symm.injective.comp
    (by intro x y h; exact congrArg Prod.fst h))
  let f : B →* Q := k.comp ((MonoidHom.inr S3 S3).comp B.subtype)
  let g : P →* Q := C.subtype.comp P.subtype
  have hf : Function.Injective f := K.subtype_injective.comp (e.symm.injective.comp
    (by intro x y h; exact Subtype.ext (congrArg Prod.snd h)))
  have hg : Function.Injective g := C.subtype_injective.comp P.subtype_injective
  have hfK : f.range ≤ K := by rintro _ ⟨x,rfl⟩; exact (e.symm _).property
  have hgC : g.range ≤ C := by rintro _ ⟨x,rfl⟩; exact x.val.property
  have hcomm (x : B) (y : P) : Commute (f x) (g y) :=
    hgC ⟨y,rfl⟩ (f x) (hfK ⟨x,rfl⟩)
  let r := f.noncommCoprod g hcomm
  have hi : Function.Injective r := (MonoidHom.noncommCoprod_injective f g hcomm).mpr
    ⟨hf,hg,(disjoint_centralizer K e).mono hfK hgC⟩
  have hp : IsPGroup 3 r.range := by
    apply IsPGroup.of_card (n := 2)
    rw [←Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,Nat.card_prod,hB,hP]
    norm_num
  have hz : r.range ≤ centralizer (j.range : Set Q) := by
    rintro _ ⟨⟨b,p⟩,rfl⟩ _ ⟨s,rfl⟩
    change j s * (f b * g p) = (f b * g p) * j s
    have hb : Commute (j s) (f b) := by
      change k (s,1) * k (1,(b:S3)) = k (1,(b:S3)) * k (s,1)
      rw [←map_mul,←map_mul]
      congr 1
    have hp : Commute (j s) (g p) := (hgC ⟨p,rfl⟩) (j s) (e.symm _).property
    exact (hb.mul_right hp).eq
  let : IsCyclic r.range := cyclic_three_subgroup_centralizing_symmetric_section
    q hq hr j hj r.range hp hz
  have hcyc : IsCyclic (B × P) := isCyclic_of_injective r.rangeRestrict
    (fun x y h => hi (congrArg Subtype.val h))
  have hcop := (Group.isCyclic_prod_iff.mp hcyc).2.2
  rw [hB,hP] at hcop
  norm_num at hcop


/-- Two-perfect {2,3}-actors in a rank-two section lie in a normal S₃ pair. -/
theorem le_pair_of_cover
    (q : D →* Q) (hq : Function.Surjective q) (hr : primeRank 3 D ≤ 2)
    (K : Subgroup Q) [K.Normal] (e : K ≃* S3 × S3)
    (B : Subgroup Q) (hB : IsPPerfect 2 B)
    (horder : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n) : B ≤ K := by
  obtain ⟨m,n,horder⟩ := horder
  let C := centralizer (K : Set Q)
  let r : Q →* Q ⧸ K := QuotientGroup.mk' K
  let f := r.comp B.subtype
  have h₁ := twoPerfect_normalizes_first K e B hB
  have h₂ := twoPerfect_normalizes_second K e B hB
  have hle : f.range ≤ C.map r := by
    rintro _ ⟨b,rfl⟩
    obtain ⟨k,hk,c,hc,he⟩ := normalizing_pair_decomposition K e b
      (h₁ b.property) (h₂ b.property)
    refine ⟨c,hc,?_⟩
    change r c = r b
    rw [he,map_mul,show r k = 1 from (QuotientGroup.eq_one_iff k).mpr hk,one_mul]
  have hnot : ¬ 3 ∣ Nat.card f.range := by
    intro hd
    exact three_not_dvd_card_centralizer_of_cover q hq hr K e
      (hd.trans ((card_dvd_of_le hle).trans (card_map_dvd C r)))
  have hcop : (Nat.card f.range).Coprime (3 ^ n) :=
    ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hnot).symm.pow_right n
  have hp : IsPGroup 2 f.range := IsPGroup.of_card_dvd_pow
    (hcop.dvd_of_dvd_mul_right ((card_range_dvd f).trans horder))
  have he := hB.hom_eq_one_of_isPGroup hp f.rangeRestrict
  intro b hb
  apply (QuotientGroup.eq_one_iff b).mp
  exact congrArg Subtype.val (DFunLike.congr_fun he (⟨b,hb⟩ : B))

/-- Inside a normal S₃ pair, every two-perfect subgroup is subnormal. -/
theorem isSubnormal_of_twoPerfect_le_pair
    (K : Subgroup Q) [K.Normal] (e : K ≃* S3 × S3)
    (B : Subgroup Q) (hB : IsPPerfect 2 B) (hBK : B ≤ K) : B.IsSubnormal := by
  let R := pResidual 2 K
  have hcard : Nat.card R = 9 := by
    rw [Nat.card_congr (e.subgroupMap R).toEquiv]
    change Nat.card ((pResidual 2 K).map e.toMonoidHom) = 9
    rw [map_pResidual_of_surjective 2 e.toMonoidHom e.surjective]
    exact SymmetricThreeProductResidual.residual_card
  let : IsMulCommutative R := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 3) (by simpa using hcard)
  have hp : IsPPerfect 2 (B.subgroupOf K) := hB.of_surjective
    (subgroupOfEquivOfLe hBK).symm.toMonoidHom (subgroupOfEquivOfLe hBK).symm.surjective
  have hBR : B.subgroupOf K ≤ R := le_pResidual_of_isPPerfect _ hp
  have hs : (B.subgroupOf K).IsSubnormal := IsSubnormal.step _ R hBR
    (inferInstance : R.Normal).isSubnormal (by infer_instance)
  exact IsSubnormal.trans hBK hs (inferInstance : K.Normal).isSubnormal

/-- The normal doubled S₃ alternative forces a two-perfect {2,3}-actor
subnormal, with the rank hypothesis kept on the actual cover. -/
theorem isSubnormal_of_twoPerfect_of_pair_cover
    (q : D →* Q) (hq : Function.Surjective q) (hr : primeRank 3 D ≤ 2)
    (K : Subgroup Q) [K.Normal] (e : K ≃* S3 × S3)
    (B : Subgroup Q) (hB : IsPPerfect 2 B)
    (horder : ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n) : B.IsSubnormal :=
  isSubnormal_of_twoPerfect_le_pair K e B hB (le_pair_of_cover q hq hr K e B hB horder)
/-- The literal cubic supplement has only the primes two and three. -/
theorem two_three_order_of_cubic_supplement
    (B : Subgroup Q) (x : Q) (hx : orderOf x = 3)
    (hg : zpowers x ⊔ B.pCoreIn 2 = B) :
    ∃ m n : ℕ, Nat.card B ∣ 2 ^ m * 3 ^ n := by
  have hxB : zpowers x ≤ B := le_sup_left.trans_eq hg
  have hn : zpowers x ≤ normalizer (B.pCoreIn 2 : Set Q) :=
    hxB.trans (B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hp := isPGroup_pCoreIn 2 B
  obtain ⟨m,hm⟩ := hp.exists_card_eq
  have hc : Nat.card (zpowers x) = 3 := (Nat.card_zpowers x).trans hx
  have hd : Disjoint (B.pCoreIn 2) (zpowers x) := hp.disjoint_of_coprime
    (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hc)) (by decide)
  have hh := card_sup_eq_mul_of_normalizes_of_disjoint (B.pCoreIn 2) (zpowers x) hn hd
  rw [sup_comm,hg,hm,hc] at hh
  exact ⟨m,1,by rw [hh,pow_one]⟩
end Theory.GroupTheory.NormalSymmetricThreePairRank

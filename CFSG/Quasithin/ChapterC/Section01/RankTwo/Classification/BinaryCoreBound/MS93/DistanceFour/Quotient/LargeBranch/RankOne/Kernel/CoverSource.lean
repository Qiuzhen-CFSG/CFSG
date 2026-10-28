module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Kernel.DisplacementSource
public import Theory.Representation.SLThreeCentralExtension.DisjointDisplacement

/-!
# The exact moving kernel from a geometric displacement

Construct the actual quotient movingSpan/U_alpha and descend conjugation
through the given source projection. Its recognized map to the marked dual
three-space is a central cover: residual commutator idempotence gives full
movement, and the splitting of Z_alpha makes its kernel fixed. Twisting by
the given marking and inverse transpose retains the exact quotient map.

A nonsplit binary natural cover has its central kernel in the displacement
of every involution. The supplied geometric involution has displacement
intersecting Z_alpha only in U_alpha, so the covering map is injective.
This proves movingSpan intersect Z_alpha = U_alpha.

Source: Meierfrankenfeld--Stellmacher (1993), (1.5)(i), p.843, and the
conversion of the orbit spans in (4.6.12), pp.910--912. The checked natural
cover theorem is cited in Theory.Representation.SLThreeCentralExtension.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
namespace Kernel
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include common in
/-- The actual two-residual acts idempotently on the orbit span. -/
theorem moving_idempotent (c : Vertex R) (hd : (cosetGraph R).dist (alpha R) c = 2) :
    ⁅movingSpan c, Ltilde R (alpha R)⁆ = movingSpan c := by
  let := finite_stabilizer R (alpha R)
  have hS : orbitSpan c ≤ Q R (alpha R) :=
    (orbitSpan_le_radius c ((cosetGraph R).dist_comm.trans hd).le).trans
      (Flags.V_le_Q geometry common.large_distance _ rfl)
  have hSl : orbitSpan c ≤ stabilizer R (alpha R) := hS.trans (fun _ h => h.1)
  have hn : pResidual 2 (stabilizer R (alpha R)) ≤
      normalizer ((orbitSpan c).subgroupOf (stabilizer R (alpha R))) := by
    intro g _
    rw [mem_normalizer_iff]
    intro x
    exact mem_normalizer_iff.mp (orbitSpan_normalized c g.property) x
  have hSp : IsPGroup 2 (orbitSpan c) :=
    (Q_isPGroup R source.two_group source.core_le (alpha R) rfl).of_injective
      (inclusion hS) (inclusion_injective hS)
  have hh := commutator_isPPerfect_idempotent (pResidual 2 (stabilizer R (alpha R)))
    ((orbitSpan c).subgroupOf (stabilizer R (alpha R))) (isPPerfect_pResidual 2)
    hSp.comap_subtype
    hn
  have hmap := congrArg (Subgroup.map (stabilizer R (alpha R)).subtype) hh
  simpa only [map_commutator, map_subgroupOf_eq_of_le hSl, movingSpan, Ltilde,
    commutator_comm] using hmap

include common radius in
/-- A geometric involution displacement removes the fixed attachment to the dual quotient. -/
theorem moving_kernel_of_separated_displacement
    (c : Vertex R) (hd : (cosetGraph R).dist (alpha R) c = 2)
    (q : SpanQuotient source common c)
    (m : M) (hm : orderOf (source.projection m) = 2)
    (hdis : ⁅orbitSpan c, zpowers (embedM R m)⁆ ⊓ Z R (alpha R) ≤ U R (alpha R)) :
    movingSpan c ⊓ Z R (alpha R) = U R (alpha R) := by
  let S := movingSpan c
  let N := (U R (alpha R)).subgroupOf S
  have hSC : S ≤ core R (alpha R) := movingSpan_le_core geometry common.large_distance c hd
  have hSl : S ≤ stabilizer R (alpha R) := hSC.trans ((core_le_Q source).trans (fun _ h => h.1))
  have hUS : U R (alpha R) ≤ S := U_le_movingSpan c hd
  have hNC : N ≤ center S := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes (alpha R) rfl)) (DistanceEight.U_le_Z R _ hx)
      y ((hSC.trans (core_le_Q source)) y.property)
  let : N.Normal := ⟨by
    intro x hx g
    simpa only [(mem_center_iff.mp (hNC hx) g), mul_inv_cancel_right] using hx⟩
  let D := S ⧸ N
  let π := QuotientGroup.mk' N
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite S := Finite.of_injective (inclusion hSl) (inclusion_injective hSl)
  have hderived : _root_.commutator S ≤ N := by
    intro x hx
    have hh := mem_map_of_mem S.subtype hx
    rw [map_subtype_commutator] at hh
    exact ((commutator_mono hSC hSC).trans
      (SmallBranch.core_derived_le_U geometry radius (alpha R) rfl)) hh
  let : IsMulCommutative D := Normal.quotient_commutative_iff_commutator_le.mpr hderived
  let : IsElementaryAbelian 2 D := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact SmallBranch.core_square_mem_U geometry radius (alpha R) rfl ⟨y, hSC y.property⟩ }
  have hPS : Mbar R ≤ normalizer S := by
    simpa only [alpha, stabilizer_m_base] using movingSpan_normalized c
  obtain ⟨a, ha⟩ := exists_quotient_conjugation_action (Mbar R) S (U R (alpha R))
    hPS common.natural.normalized inferInstance
  let ι : M →* Mbar R := (embedM R).rangeRestrict
  let aM : M →* MulAut D := a.comp ι
  have hkill : source.projection.ker ≤ aM.ker := by
    intro n hn
    have hnQ : embedM R n ∈ Q R (alpha R) := by
      rw [Q_alpha R source.two_group source.core_le]
      exact mem_map_of_mem _ (source.projection_kernel ▸ hn)
    exact quotient_conjugation_action_kills_commutator_layer (Mbar R) S (U R (alpha R))
      (Q R (alpha R)) inferInstance hPS
      ((commutator_mono hSC le_rfl).trans (SmallBranch.core_commutator_Q_le_U
        source geometry common radius (alpha R) (beta R) rfl (base_adjacent R))) a ha hnQ
  let aSL : SL →* MulAut D := source.projection.liftOfSurjective
    source.projection_surjective ⟨aM, hkill⟩
  have haSL (n : M) : aSL (source.projection n) = aM n :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let : MulDistribMulAction SL D := MulDistribMulAction.compHom D aSL
  let ρ : Representation (ZMod 2) SL (Additive D) := ofElementaryAbelianAction
  let τ := Seed.dualTwist common.natural.marking
  let σ : Representation (ZMod 2) SL (Additive D) := ρ.comp τ.toMonoidHom
  let f := q.quotient.comp (inclusion (movingSpan_le_span c))
  have hNf : N ≤ f.ker := by
    intro x hx
    change inclusion (movingSpan_le_span c) x ∈ q.quotient.ker
    rw [q.kernel]
    exact DistanceEight.U_le_Z R _ hx
  let fD : D →* Multiplicative Linear.W := QuotientGroup.lift N f hNf
  let p₀ : Additive D →ₗ[ZMod 2] Linear.W := fD.toAdditiveLeft.toZModLinearMap 2
  have hpπ (x : S) : p₀ (Additive.ofMul (π x)) = (f x).toAdd := rfl
  let conjugate (n : M) (x : S) : S :=
    ⟨embedM R n * x * (embedM R n)⁻¹,
      (mem_normalizer_iff.mp (hPS ⟨n, rfl⟩) x).mp x.property⟩
  have hact (n : M) (x : S) :
      ρ (source.projection n) (Additive.ofMul (π x)) =
        Additive.ofMul (π (conjugate n x)) := by
    change aSL (source.projection n) (π x) = π (conjugate n x)
    rw [haSL]
    exact ha (ι n) x
  have hequiv (g : SL) (v : Additive D) :
      p₀ (ρ g v) = Linear.dual (common.natural.marking g) (p₀ v) := by
    obtain ⟨n, rfl⟩ := source.projection_surjective g
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N v.toMul
    have hv : v = Additive.ofMul (π x) := congrArg Additive.ofMul hx.symm
    rw [hv, hact, hpπ, hpπ]
    exact q.action n (inclusion (movingSpan_le_span c) x)
      (inclusion (movingSpan_le_span c) (conjugate n x)) rfl
  let p : σ.IntertwiningMap BinaryLinearThree.W := {
    toLinearMap := p₀
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      change p₀ (ρ (τ g) v) = BinaryLinearThree.W g (p₀ v)
      rw [hequiv]
      change Linear.dual (common.natural.marking
        (common.natural.marking.symm (BinaryLinearThree.AutomorphismAction.graph g))) (p₀ v) = _
      rw [MulEquiv.apply_symm_apply]
      change BinaryLinearThree.W (BinaryLinearThree.AutomorphismAction.graph
        (BinaryLinearThree.AutomorphismAction.graph g)) (p₀ v) = _
      rw [BinaryLinearThree.AutomorphismAction.graph_graph] }
  have hponto : Function.Surjective p := by
    intro w
    obtain ⟨x, hx⟩ := q.moving_onto (Multiplicative.ofAdd w)
    exact ⟨Additive.ofMul (π x), congrArg Multiplicative.toAdd hx⟩
  have hpfixed : p.toLinearMap.ker ≤ fixed σ := by
    intro v hv g
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N v.toMul
    have hvx : v = Additive.ofMul (π x) := congrArg Additive.ofMul hx.symm
    have hxZ : (x : FreeAmalgam R) ∈ Z R (alpha R) := by
      have he : f x = 1 := by
        apply Multiplicative.toAdd.injective
        change p v = 0 at hv
        rw [hvx] at hv
        exact hv
      change inclusion (movingSpan_le_span c) x ∈ (Z R (alpha R)).subgroupOf (orbitSpan c)
      rw [← q.kernel]
      exact he
    obtain ⟨n, hn⟩ := source.projection_surjective (τ g)
    change ρ (τ g) v = v
    rw [← hn, hvx, hact]
    apply congrArg Additive.ofMul
    apply (mul_inv_eq_one).mp
    rw [← map_inv, ← map_mul]
    change (QuotientGroup.mk' N) (conjugate n x * x⁻¹) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hc := Flags.RankOne.Z_stabilizer_commutator_le_U source geometry common
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator (show embedM R n ∈ stabilizer R (alpha R) by
      rw [alpha, stabilizer_m_base]; exact ⟨n, rfl⟩) hxZ)
  have hpfull : Coinvariants.ker σ = ⊤ := by
    let H : Subgroup S := (Coinvariants.ker σ).toAddSubgroup.toSubgroup'.comap π
    have hSH : S ≤ H.map S.subtype := by
      change movingSpan c ≤ H.map S.subtype
      rw [← moving_idempotent common c hd, commutator_comm]
      apply commutator_le.mpr
      intro l hl x hx
      have hlM : l ∈ Mbar R := by
        rw [← stabilizer_m_base R]
        exact map_subtype_le _ hl
      obtain ⟨n, rfl⟩ := hlM
      let z : S := conjugate n ⟨x, hx⟩ * (⟨x, hx⟩ : S)⁻¹
      refine ⟨z, ?_, rfl⟩
      change Additive.ofMul (π z) ∈ Coinvariants.ker σ
      have hz : Additive.ofMul (π z) =
          σ (τ.symm (source.projection n)) (Additive.ofMul (π ⟨x, hx⟩)) -
            Additive.ofMul (π ⟨x, hx⟩) := by
        change Additive.ofMul (π (conjugate n ⟨x, hx⟩ * (⟨x, hx⟩ : S)⁻¹)) =
          ρ (τ (τ.symm (source.projection n))) _ - _
        rw [MulEquiv.apply_symm_apply, hact, map_mul, map_inv]
        rw [sub_eq_add_neg]
        rfl
      rw [hz]
      exact Coinvariants.sub_mem_ker _ _
    apply top_unique
    intro v _
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N v.toMul
    obtain ⟨y, hy, he⟩ := hSH x.property
    have he' : y = x := Subtype.ext he
    subst y
    change Additive.ofMul (π x) ∈ Coinvariants.ker σ at hy
    rwa [hx] at hy
  have hp : IsCover p := ⟨hponto, hpfixed, hpfull⟩
  let t := τ.symm (source.projection m)
  have ht : orderOf t = 2 := (τ.symm.orderOf_eq _).trans hm
  have hlinDis : Disjoint p.toLinearMap.ker (LinearMap.range (σ t - LinearMap.id)) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hr
    obtain ⟨w, rfl⟩ := hr
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N w.toMul
    have hw : w = Additive.ofMul (π x) := congrArg Additive.ofMul hx.symm
    have htact : σ t w = Additive.ofMul (π (conjugate m x)) := by
      change ρ (τ (τ.symm (source.projection m))) w = _
      rw [MulEquiv.apply_symm_apply, hw, hact]
    let z : S := conjugate m x * x⁻¹
    have hz : (σ t - (LinearMap.id : Additive D →ₗ[ZMod 2] Additive D)) w =
        Additive.ofMul (π z) := by
      change σ t w - w = _
      rw [htact, hw]
      change _ = Additive.ofMul (π (conjugate m x * x⁻¹))
      rw [map_mul, map_inv]
      rw [sub_eq_add_neg]
      rfl
    have hzZ : (z : FreeAmalgam R) ∈ Z R (alpha R) := by
      rw [hz] at hv
      have he : f z = 1 := Multiplicative.toAdd.injective hv
      change inclusion (movingSpan_le_span c) z ∈ (Z R (alpha R)).subgroupOf (orbitSpan c)
      rw [← q.kernel]
      exact he
    have hzU : (z : FreeAmalgam R) ∈ U R (alpha R) := by
      apply hdis
      refine ⟨?_, hzZ⟩
      change ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ _
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_zpowers _) (movingSpan_le_span c x.property)
    rw [hz]
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff z).mpr hzU)
  have hbij := SLThreeCentralExtension.cover_bijective_of_disjoint_involution_displacement
    σ p hp t ht hlinDis
  apply le_antisymm
  · intro x hx
    let xS : S := ⟨x, hx.1⟩
    have hpx : p (Additive.ofMul (π xS)) = 0 := by
      have he : f xS = 1 := by
        change inclusion (movingSpan_le_span c) xS ∈ q.quotient.ker
        rw [q.kernel]
        exact hx.2
      exact congrArg Multiplicative.toAdd he
    have hzero : Additive.ofMul (π xS) = 0 := hbij.1 (hpx.trans (map_zero p).symm)
    exact (QuotientGroup.eq_one_iff xS).mp (congrArg Additive.toMul hzero)
  · exact le_inf hUS (DistanceEight.U_le_Z R _)

end Kernel
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne

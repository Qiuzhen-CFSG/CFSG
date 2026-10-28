module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Actions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Linear
public import Theory.GroupAction.SubgroupQuotientCommutatorImage
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.Displacement

/-!
# Displacement under the original source projection

An ambient actor in G_a maps to SL3(2) through the original projection.
Its displacement on the literal orbit quotient is the relative index of
its ambient commutator. The same actor's displacement under the prescribed
natural marking is the cardinal of its commutator with U_a.

A product A Q_a = Q_t for an actual incident edge has image of order four
and natural displacement of order four. If the quotient displacement is
at most two, Cauchy's theorem selects an actual nonidentity involution in
that image, giving both the small-involution and orientation tests. No
involutory lift, faithfulness, or full movement is assumed.

The source application for d is in First; DeltaBounds gives the transported
index bound and a conditional delta consumer. Constructing delta's actor
and justifying its edge product remain separate geometric obligations.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii), printed p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement
variable {M : Type*} [Group M] {R L : Subgroup M}

private theorem conjugation_image {G E S : Type*} [Group G] [Group E] [Group S]
    (φ : M →* G) (π : M →* S) (ρ : S →* MulAut E)
    (H A : Subgroup G) (hH : φ.range ≤ normalizer H) (hA : A ≤ φ.range)
    (f : H →* E) (hf : Function.Surjective f)
    (hc : ∀ (m : M) (x y : H), (y : G) = φ m * (x : G) * (φ m)⁻¹ →
      ρ (π m) (f x) = f y) :
    commutatorAction (((A.comap φ).map π).map ρ) E =
      (⁅H, A⁆.subgroupOf H).map f := by
  have hn := hA.trans hH
  apply le_antisymm
  · rw [commutatorAction_eq_closure, closure_le]
    rintro _ ⟨⟨σ, g, ⟨m, hm, rfl⟩, rfl⟩, x, rfl⟩
    obtain ⟨u, rfl⟩ := hf x
    let w : H := ⟨φ m * (u : G) * (φ m)⁻¹,
      (mem_normalizer_iff.mp (hH ⟨m, rfl⟩) u).mp u.property⟩
    change (f u)⁻¹ * ρ (π m) (f u) ∈ _
    rw [hc m u w rfl, ← map_inv, ← map_mul]
    apply mem_map_of_mem
    change (u : G)⁻¹ * (φ m * (u : G) * (φ m)⁻¹) ∈ ⁅H,A⁆
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using
      commutator_mem_commutator (H.inv_mem u.property) hm
  · let C := commutatorAction (((A.comap φ).map π).map ρ) E
    have hh : ⁅H,A⁆ ≤ (C.comap f).map H.subtype := by
      apply commutator_le.mpr
      intro x hx a ha
      obtain ⟨m, hm⟩ := hA ha
      subst a
      let u : H := ⟨x, hx⟩
      let w : H := ⟨φ m * (u⁻¹ : H) * (φ m)⁻¹,
        (mem_normalizer_iff.mp (hH ⟨m, rfl⟩) u⁻¹).mp (H.inv_mem hx)⟩
      have hu : ⁅x, φ m⁆ ∈ H :=
        (le_normalizer_iff_commutator_le_left.mp hn) (commutator_mem_commutator hx ha)
      refine ⟨⟨⁅x, φ m⁆, hu⟩, ?_, rfl⟩
      have he : (f u⁻¹)⁻¹ * ρ (π m) (f u⁻¹) = f ⟨⁅x, φ m⁆, hu⟩ := by
        rw [hc m u⁻¹ w rfl, ← map_inv, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [u, w, coe_mul, coe_inv, inv_inv, commutatorElement_def, mul_assoc]
      change f ⟨⁅x, φ m⁆, hu⟩ ∈ C
      rw [← he]
      dsimp only [C]
      rw [commutatorAction_eq_closure]
      exact subset_closure ⟨⟨ρ (π m), mem_map_of_mem _ (mem_map_of_mem _ ha)⟩, f u⁻¹, rfl⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hh hx
    exact (show y = x from Subtype.ext hxy) ▸ hy

/-- The literal image of an ambient actor in the original matrix quotient. -/
@[expose] def actorImage (source : LocalSource L R) (A : Subgroup (FreeAmalgam R)) : Subgroup SL :=
  (A.comap (embedM R)).map source.projection

/-- The quotient displacement is computed by its ambient commutator. -/
theorem orbit_displacement_card (source : LocalSource L R)
    {p : Higher.SourcePath (alpha R)} {v : Vertex R}
    (s : OrbitModule source p v) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ Mbar R) : letI := s.normal
    Nat.card (commutatorAction ((actorImage source A).map s.action) (OrbitSpace p v)) =
      (hatV R (alpha R) (p.walk.getVert 6)).relIndex ⁅orbitFactor p v,A⁆ := by
  let := s.normal
  have hn : Mbar R ≤ normalizer (orbitFactor p v) := by
    simpa only [alpha, stabilizer_m_base] using orbitFactor_normalized p v
  rw [actorImage, conjugation_image (embedM R) source.projection s.action
    (orbitFactor p v) A hn hA (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    s.conjugation, ← relIndex_ker, QuotientGroup.ker_mk',
    relIndex_subgroupOf (le_normalizer_iff_commutator_le_left.mp (hA.trans hn))]

/-- The original natural marking transports the actual U displacement. -/
theorem natural_displacement_card (source : LocalSource L R)
    (natural : NaturalU R source.projection) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ Mbar R) :
    Nat.card (commutatorAction ((actorImage source A).map (naturalAction natural.marking))
      (Multiplicative (Fin 3 → ZMod 2))) = Nat.card (⁅U R (alpha R), A⁆ : Subgroup (FreeAmalgam R)) := by
  have hc : ∀ (m : M) (x y : U R (alpha R)),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      naturalAction natural.marking (source.projection m) (natural.equiv x) = natural.equiv y := by
    intro m x y hy
    exact Multiplicative.toAdd.injective (natural.action m x y hy).symm
  rw [actorImage, conjugation_image (embedM R) source.projection
    (naturalAction natural.marking) (U R (alpha R)) A natural.normalized hA
    natural.equiv.toMonoidHom natural.equiv.surjective hc]
  exact (Nat.card_congr ((⁅U R (alpha R), A⁆.subgroupOf (U R (alpha R))).equivMapOfInjective
    natural.equiv.toMonoidHom natural.equiv.injective).toEquiv).symm.trans
      (Nat.card_congr (subgroupOfEquivOfLe
        (le_normalizer_iff_commutator_le_left.mp (hA.trans natural.normalized))).toEquiv)


/-- The actual image cardinal, with no ambient finiteness assumption. -/
theorem actorImage_card [Finite M] (source : LocalSource L R)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Mbar R) :
    Nat.card (actorImage source A) = (Q R (alpha R)).relIndex A := by
  rw [actorImage, ← relIndex_ker, source.projection_kernel,
    ← relIndex_map_map_of_injective (pCore 2 M) (A.comap (embedM R)) (embedM_injective R),
    ← Q_alpha R source.two_group source.core_le, map_comap_eq_self hA]

private theorem product_join {G : Type*} [Group G] {A Q T : Subgroup G}
    (h : (A : Set G) * (Q : Set G) = (T : Set G)) : Q ⊔ A = T := by
  have hA : A ≤ T := by
    intro a ha
    rw [← SetLike.mem_coe, ← h]
    exact ⟨a, ha, 1, Q.one_mem, mul_one a⟩
  have hQ : Q ≤ T := by
    intro q hq
    rw [← SetLike.mem_coe, ← h]
    exact ⟨1, A.one_mem, q, hq, one_mul q⟩
  refine le_antisymm (sup_le hQ hA) ?_
  intro x hx
  change x ∈ (T : Set G) at hx
  rw [← h] at hx
  obtain ⟨a, ha, q, hq, rfl⟩ := hx
  exact (Q ⊔ A).mul_mem ((show A ≤ Q ⊔ A from le_sup_right) ha) ((show Q ≤ Q ⊔ A from le_sup_left) hq)

/-- The source product computes the image under the ORIGINAL projection. -/
theorem actorImage_eq_of_product [Finite M] (source : LocalSource L R)
    {A T : Subgroup (FreeAmalgam R)} (hT : T ≤ Mbar R)
    (hprod : (A : Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (T : Set (FreeAmalgam R))) : actorImage source A = actorImage source T := by
  have hj := product_join hprod
  have hQ : Q R (alpha R) ≤ Mbar R := le_sup_left.trans hj.le |>.trans hT
  have hA : A ≤ Mbar R := le_sup_right.trans hj.le |>.trans hT
  have hk : actorImage source (Q R (alpha R)) = ⊥ := by
    rw [actorImage, Q_alpha R source.two_group source.core_le,
      comap_map_eq_self_of_injective (embedM_injective R), ← source.projection_kernel,
      map_ker_self]
  unfold actorImage at hk ⊢
  rw [← hj, ← comap_sup_eq_of_le_range (embedM R) hQ hA, Subgroup.map_sup, hk, bot_sup_eq]

/-- An edge product has order-four displacement on the fixed natural module.
This uses the actual edge action, so the source marking is preserved. -/
theorem edge_product_natural_card [Finite M] (source : LocalSource L R)
    {geometry : Geometry R} (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {t : Vertex R} (ht : Adjacent R (alpha R) t)
    {A : Subgroup (FreeAmalgam R)}
    (hprod : (A : Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R))) :
    Nat.card (commutatorAction ((actorImage source A).map (naturalAction common.natural.marking))
      (Multiplicative (Fin 3 → ZMod 2))) = 4 ∧ Nat.card (actorImage source A) = 4 := by
  have hT : Q R t ≤ Mbar R := by
    simpa only [alpha, stabilizer_m_base] using
      (show Q R t ≤ stabilizer R (alpha R) from fun _ hx => hx.2 _ (adjacent_symm R ht))
  have hi := actorImage_eq_of_product source hT hprod
  rw [hi, natural_displacement_card source common.natural _ hT, actorImage_card source _ hT]
  rw [← Escape.EdgeTransfer.edge_commutator_eq_natural common.large_distance
    (PathCentrality.LocalCommutator.moduleFacts common) (alpha R) t rfl ht]
  exact ⟨Early.First.Layer.edge_displacement_card common earlier rfl ht,
    earlier.edge_Q_index _ _ rfl ht⟩

/-- Extract an actual involution from an order-four image and apply the
literal ambient commutator bound. No involutory lift in M is assumed. -/
theorem small_and_separated_of_edge_product [Finite M] (source : LocalSource L R)
    {geometry : Geometry R} (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)} {v t : Vertex R}
    (s : OrbitModule source p v) (ht : Adjacent R (alpha R) t)
    {A : Subgroup (FreeAmalgam R)}
    (hprod : (A : Set (FreeAmalgam R)) * (Q R (alpha R) : Set (FreeAmalgam R)) =
      (Q R t : Set (FreeAmalgam R)))
    (hbound : (hatV R (alpha R) (p.walk.getVert 6)).relIndex ⁅orbitFactor p v, A⁆ ≤ 2) :
    letI := s.normal
    Escape.Initial.Natural.Splitting.HasSmallInvolution s.action ∧
      DisplacementSeparation s.action common.natural.marking := by
  let := s.normal
  let := s.finite
  have hT : Q R t ≤ Mbar R := by
    simpa only [alpha, stabilizer_m_base] using
      (show Q R t ≤ stabilizer R (alpha R) from fun _ hx => hx.2 _ (adjacent_symm R ht))
  have hA : A ≤ Mbar R := (le_sup_right.trans (product_join hprod).le).trans hT
  have hs : Nat.card (commutatorAction ((actorImage source A).map s.action) (OrbitSpace p v)) ≤ 2 := by
    rw [orbit_displacement_card source s A hA]
    exact hbound
  obtain ⟨hnat, hcard⟩ := edge_product_natural_card source common earlier ht hprod
  constructor
  · obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := actorImage source A) 2
      (by rw [hcard]; decide)
    have hne : (t : SL) ≠ 1 := by
      intro he
      have he' : t = 1 := Subtype.ext he
      simp only [he', orderOf_one] at ht
      omega
    have hp : (t : SL) ^ 2 = 1 := by
      have he := pow_orderOf_eq_one t
      rw [ht] at he
      exact congrArg Subtype.val he
    refine ⟨t, hne, hp, ?_⟩
    exact (card_le_of_le (Escape.Initial.Natural.Splitting.displacement_mono
      (zpowers_le.mpr (mem_map_of_mem s.action t.property)))).trans hs
  · refine ⟨actorImage source A, ?_⟩
    rw [hnat]
    omega


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Displacement

module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Commutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Linear
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Marked

/-!
# The literal neighboring quotient action and its geometric consumer

Conjugation by Q_a acts on the actual second layer at c. The local turn
identifies that layer with the G_c-span of the backward first layer at a.
In the compatible marked doubled-dual quotient, its image is fixed by
Q_a and generates under SL₃(2). The actual actor has order four and fixes
the natural plane U_c intersect Z_t. The binary fixed-seed theorem therefore
puts every quotient displacement in the image of the backward first layer.
Lifting through the exact first-layer kernel gives
[hat W_c,Q_a] ≤ hat V_a ⊔ hat V_c, with a subgroup join. The final export
applies this estimate to both ordered products of the Z-case consumer.

The genuine marked section remains an explicit source input from
`qt-c01-ms93-higher-marked-quotients`. The literal (4.5.3)(i) first-layer
identities at a and d and the (4.5.1)(v) cardinal |H_a|=4 remain inputs from
`qt-c01-ms93-core-factors-early-layers`. Their discharge belongs to the
parent source assembly. The section uses the same CommonFacts marking,
pulled back by an actual conjugator, and retains both forward vertices.
No (4.5.5), Z-case conclusion, conjugate-pair bound, global derived/Q bound,
or erroneous OrbitFacts generation premise is used.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)--(4.5.5), pp.898--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Literal left conjugation by Q_a on the second layer based at c. -/
noncomputable def quotientActor [Finite M] {a : Vertex R} (p : Higher.SourcePath a) :
    Q R a →* MulAut (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) :=
  Offenders.conjugation _ _ (second_normalized_by_neighbor p)

/-- The action uses left conjugation in the ambient amalgam. -/
theorem quotientActor_apply [Finite M] {a : Vertex R} (p : Higher.SourcePath a)
    (q : Q R a)
    (x : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) :
    (quotientActor p q x : FreeAmalgam R) =
      (q : FreeAmalgam R) * (x : FreeAmalgam R) * (q : FreeAmalgam R)⁻¹ := by
  rfl

/-- In every quotient with the literal first-layer kernel, Q_a fixes the
image of the backward first-layer seed. -/
theorem quotient_seed_fixed [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : Higher.SourcePath a)
    (hVa : hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a)
    {T : Type*} [Group T]
    (φ : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) →* T)
    (hker : φ.ker = (hatV R (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
      (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)))
    (q : Q R a)
    (x : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))
    (hx : (x : FreeAmalgam R) ∈ hatV R a (p.walk.getVert 6)) :
    φ (quotientActor p q x) = φ x := by
  have hk : quotientActor p q x * x⁻¹ ∈ φ.ker := by
    rw [hker]
    change (q : FreeAmalgam R) * (x : FreeAmalgam R) * (q : FreeAmalgam R)⁻¹ *
      (x : FreeAmalgam R)⁻¹ ∈ hatV R (p.walk.getVert 6) (p.walk.getVert 8)
    have hh := first_action_le_neighbor_first common earlier p hVa
    rw [commutator_comm] at hh
    exact hh (commutator_mem_commutator q.property hx)
  exact mul_inv_eq_one.mp (by simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hk)

private theorem lift_image {G T : Type*} [Group G] [Group T]
    {W A N : Subgroup G} (φ : W →* T) (hk : φ.ker = N.subgroupOf W)
    (x : W) (hx : φ x ∈ (A.subgroupOf W).map φ) : (x : G) ∈ A ⊔ N := by
  obtain ⟨y,hy,he⟩ := hx
  have hxy : x * y⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
  rw [hk] at hxy
  have hh := (A ⊔ N).mul_mem (mem_sup_right hxy) (mem_sup_left hy)
  change (x : G) * (y : G)⁻¹ * (y : G) ∈ A ⊔ N at hh
  simpa only [inv_mul_cancel_right] using hh

/-- Lift a displacement calculation through its exact quotient map. This
does not assert the remaining representation-theoretic image containment. -/
theorem neighbor_bound_of_quotient_displacement [Finite M] {a : Vertex R} (p : Higher.SourcePath a)
    {T : Type*} [Group T]
    (φ : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) →* T)
    (hker : φ.ker = (hatV R (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
      (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)))
    (himage : ∀ (q : Q R a)
      (x : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)),
      φ (x * (quotientActor p q x)⁻¹) ∈
        ((hatV R a (p.walk.getVert 6)).subgroupOf
          (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))).map φ) :
    ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R a⁆ ≤
      hatV R a (p.walk.getVert 6) ⊔ hatV R (p.walk.getVert 6) (p.walk.getVert 8) := by
  apply commutator_le.mpr
  intro x hx q hq
  have h := lift_image φ hker _ (himage ⟨q,hq⟩ ⟨x,hx⟩)
  change x * (q * x * q⁻¹)⁻¹ ∈ _ at h
  simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, commutatorElement_def] using h

/-- The exact quotient displacement feeds both ordered products in the
existing geometric consumer, with all three moving vertices retained. -/
theorem pair_products_of_quotient_displacement [Finite M]
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    {T : Type*} [Group T]
    (φ : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) →* T)
    (hker : φ.ker = (hatV R (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
      (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)))
    (himage : ∀ (q : Q R a)
      (x : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)),
      φ (x * (quotientActor p q x)⁻¹) ∈
        ((hatV R a (p.walk.getVert 6)).subgroupOf
          (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))).map φ)
    (g : stabilizer R a) :
    ((⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ⊆
      ((hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) *
        (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R))) ∩
      ((hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) : Set (FreeAmalgam R)) *
        (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R))) :=
  pair_commutator_products_of_neighbor_bound earlier p
    (neighbor_bound_of_quotient_displacement p φ hker himage) g

open DistanceFour.Linear

/-- The local turn makes the image of the backward first layer generate
the actual doubled-dual quotient under the marked local action. -/
theorem quotient_seed_generates
    {common : CommonFacts R source geometry} (p : Higher.SourcePath (alpha R))
    {g : FreeAmalgam R} (coords : Marked.Data common p g)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (D : Subgroup (Multiplicative (W × W)))
    (hseed : ((hatV R (alpha R) (p.walk.getVert 6)).subgroupOf
      (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))).map coords.quotient ≤ D)
    (hD : ∀ k : S, ∀ v ∈ D,
      Multiplicative.ofAdd (dual k v.toAdd.1, dual k v.toAdd.2) ∈ D) : D = ⊤ := by
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let B := hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)
  have ht : ∃ k ∈ stabilizer R (p.walk.getVert 6), act R k (p.walk.getVert 8) = alpha R := by
    simpa only [p.center_eq] using p.turns 6 (by decide) (by decide) (by decide)
  have hAB : A ≤ B := hatV_le_next_hatW hVa hVd ht
  let N : Subgroup (FreeAmalgam R) := (D.comap coords.quotient).map B.subtype
  have hBN : B ≤ N := by
    change hatW R _ _ _ ≤ N
    rw [second_eq_backward_span hVa hVd ht]
    apply iSup_le
    intro k
    rintro z ⟨x, hx, rfl⟩
    let xB : B := ⟨x, hAB hx⟩
    let yB : B := Offenders.conjugation (stabilizer R (p.walk.getVert 6)) B
      (hatW_normalized R _ _ _) k⁻¹ xB
    refine ⟨yB, ?_, rfl⟩
    change coords.quotient yB ∈ D
    have ha := coords.quotient_action k⁻¹ xB yB rfl
    have he : coords.quotient yB = Multiplicative.ofAdd
        (dual (coords.projection k⁻¹) (coords.quotient xB).toAdd.1,
          dual (coords.projection k⁻¹) (coords.quotient xB).toAdd.2) :=
      Multiplicative.toAdd.injective ha
    rw [he]
    exact hD _ _ (hseed (mem_map_of_mem coords.quotient hx))
  apply top_unique
  intro v _
  obtain ⟨x, rfl⟩ := coords.quotient_onto v
  obtain ⟨y, hy, he⟩ := hBN x.property
  have hxy : y = x := Subtype.ext he
  subst y
  exact hy


/-- In the actual marked quotient, every neighboring-kernel displacement
belongs to the image of the backward first layer. -/
theorem quotient_displacement [Finite M]
    {common : CommonFacts R source geometry} (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R)) {g : FreeAmalgam R}
    (coords : Marked.Data common p g)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (q : Q R (alpha R))
    (x : hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) :
    coords.quotient (x * (quotientActor p q x)⁻¹) ∈
      ((hatV R (alpha R) (p.walk.getVert 6)).subgroupOf
        (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))).map coords.quotient := by
  let E := ((hatV R (alpha R) (p.walk.getVert 6)).subgroupOf
    (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))).map coords.quotient
  let K := ((Q R (alpha R)).subgroupOf (stabilizer R (p.walk.getVert 6))).map coords.projection
  have hfix : ∀ k ∈ K, ∀ v ∈ E,
      Multiplicative.ofAdd (dual k v.toAdd.1, dual k v.toAdd.2) = v := by
    rintro k ⟨r, hr, rfl⟩ v ⟨y, hy, rfl⟩
    let rQ : Q R (alpha R) := ⟨r, hr⟩
    have ha := coords.quotient_action r y (quotientActor p rQ y) rfl
    have hf := quotient_seed_fixed common earlier p hVa coords.quotient
      coords.quotient_kernel rQ y hy
    apply Multiplicative.toAdd.injective
    exact ha.symm.trans (congrArg Multiplicative.toAdd hf)
  have hq : (q : FreeAmalgam R) ∈ stabilizer R (p.walk.getVert 6) :=
    Q_le_stabilizer_of_dist_two R (alpha R) (p.walk.getVert 6) rfl
      (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.1) q.property
  let qc : stabilizer R (p.walk.getVert 6) := ⟨q, hq⟩
  have hk : coords.projection qc ∈ K := mem_map_of_mem coords.projection q.property
  have hd := Linear.displacement_mem_of_fixed_generating_seed K coords.plane
    coords.actor_card coords.plane_card coords.actor_fixes_plane E hfix
    (quotient_seed_generates p coords hVa hVd) hk (coords.quotient x)
  have ha := coords.quotient_action qc x (quotientActor p q x) rfl
  have he : coords.quotient (quotientActor p q x) = Multiplicative.ofAdd
      (dual (coords.projection qc) (coords.quotient x).toAdd.1,
        dual (coords.projection qc) (coords.quotient x).toAdd.2) :=
    Multiplicative.toAdd.injective ha
  simpa only [map_mul, map_inv, he] using hd

/-- The neighboring quotient-action estimate from the actual pulled-back
marked section and literal preceding-source statements. -/
theorem neighbor_bound [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R))
    (g : FreeAmalgam R) (hg : act R g (alpha R) = p.walk.getVert 6)
    (s : MarkedPairSection source common
      (rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁻¹)
      (rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) g⁻¹) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hH : Nat.card (H R (alpha R)) = 4) :
    ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R (alpha R)⁆ ≤
      hatV R (alpha R) (p.walk.getVert 6) ⊔ hatV R (p.walk.getVert 6) (p.walk.getVert 8) := by
  let coords := Marked.data common earlier p g hg s hVa hH
  exact neighbor_bound_of_quotient_displacement p coords.quotient coords.quotient_kernel
    (quotient_displacement earlier p coords hVa hVd)

/-- Application of the neighboring estimate to both ordered products for
every actual conjugate of the second layer. -/
theorem pair_products [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    (p : Higher.SourcePath (alpha R))
    (g : FreeAmalgam R) (hg : act R g (alpha R) = p.walk.getVert 6)
    (s : MarkedPairSection source common
      (rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁻¹)
      (rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) g⁻¹) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hH : Nat.card (H R (alpha R)) = 4) (k : stabilizer R (alpha R)) :
    ((⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) k⁆ :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ⊆
      ((hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) *
        (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R))) ∩
      ((hatV R (act R k (p.walk.getVert 6)) (act R k (p.walk.getVert 8)) : Set (FreeAmalgam R)) *
        (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R))) :=
  pair_commutator_products_of_neighbor_bound earlier p
    (neighbor_bound common earlier p g hg s hVa hVd hH) k

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction

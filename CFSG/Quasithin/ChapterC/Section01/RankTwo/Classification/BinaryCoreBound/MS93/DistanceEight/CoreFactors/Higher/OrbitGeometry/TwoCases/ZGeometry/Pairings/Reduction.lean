module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Characters

/-!
# Reduction of edge images to local commutator bounds

An invariant character vanishes on the commutator with its acting subgroup.
The constructed characters also vanish on the fixed summand. Thus an edge
contained in their join is annihilated whenever the neighboring layer is fixed
modulo the lower layer. The binary edge index makes its character group have
order two: the nonzero first-layer image is therefore the entire annihilator.
Its nonvanishing follows from the literal orbit generation and quotient
surjectivity, rather than from a dimension label.

EdgeDisplacements retains the three still unproved group-theoretic bounds.
They are transported simultaneously with every path vertex. The first-edge
comparison is exported independently of the second-layer bound, so it can be
used in constructing that bound without a circular argument. The final two
exports apply the resulting comparisons to the existing geometric consumers.

This is a conditional reduction, not a proof that EdgeDisplacements exists.
The marked quotient producers remain qt-c01-ms93-higher-marked-quotients;
preceding literal (4.5.1)--(4.5.3) facts belong to the early-layer producer.
No erroneous Early.OrbitFacts or core-factor conclusion is used.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.5), printed p.899,
with the relative-normalizer convention on p.881.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings
open DistanceFour.Linear
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R} (common : CommonFacts R source geometry)

open scoped commutatorElement

private theorem characterMap_edge_of_displacement
    {A N D K : Subgroup (FreeAmalgam R)} {t : Vertex R}
    (f : A →* (Z R (alpha R) →* Multiplicative (ZMod 2)))
    (hAn : Mbar R ≤ normalizer A) (hN : N.subgroupOf A ≤ f.ker)
    (hfix : ∀ (x : A) (z : Z R (alpha R)),
      (z : FreeAmalgam R) ∈ fixedSummand (R := R) → f x z = 1)
    (hact : ∀ (m : M) (x y : A) (z w : Z R (alpha R)),
      (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
      (w : FreeAmalgam R) = embedM R m * (z : FreeAmalgam R) * (embedM R m)⁻¹ →
      f y w = f x z)
    (hK : K ≤ Mbar R) (hmove : ⁅D, K⁆ ≤ N)
    (hspan : Z R t ≤ ⁅Z R (alpha R), K⁆ ⊔ fixedSummand (R := R))
    (x : A) (hx : (x : FreeAmalgam R) ∈ D) :
    f x ∈ edgeCharacters (alpha R) t := by
  let H := ((f x).ker).map (Z R (alpha R)).subtype
  have hfixed : fixedSummand (R := R) ≤ H := by
    intro z hz
    exact ⟨⟨z,hz.1⟩, hfix x _ hz, rfl⟩
  have hcomm : ⁅Z R (alpha R), K⁆ ≤ H := by
    apply commutator_le.mpr
    intro z hz k hk
    obtain ⟨m, hm⟩ := hK hk
    subst k
    have hmS : embedM R m ∈ stabilizer R (alpha R) := by
      rw [alpha, stabilizer_m_base]
      exact ⟨m,rfl⟩
    let y : A := ⟨embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹,
      le_normalizer_iff.mp hAn _ ⟨m,rfl⟩ _ x.property⟩
    let z₀ : Z R (alpha R) := ⟨z,hz⟩
    let w : Z R (alpha R) := ⟨embedM R m * z * (embedM R m)⁻¹,
      le_normalizer_iff.mp (Z_normalized R _) _ hmS _ hz⟩
    have hyker : y * x⁻¹ ∈ f.ker := by
      apply hN
      change embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ * (x : FreeAmalgam R)⁻¹ ∈ N
      have h := hmove
      rw [commutator_comm] at h
      exact h (commutator_mem_commutator hk hx)
    have hxy : f y = f x := by
      have h := MonoidHom.mem_ker.mp hyker
      rw [map_mul, map_inv, mul_inv_eq_one] at h
      exact h
    have hw : f x w = f x z₀ := by
      simpa only [hxy] using hact m x y z₀ w rfl rfl
    refine ⟨z₀ * w⁻¹, ?_, ?_⟩
    · change f x (z₀ * w⁻¹) = 1
      rw [map_mul, map_inv, hw, mul_inv_cancel]
    · change z * (embedM R m * z * (embedM R m)⁻¹)⁻¹ = ⁅z, embedM R m⁆
      simp only [commutatorElement_def, mul_inv_rev, inv_inv]
      group
  intro z hz
  obtain ⟨w,hw,he⟩ := (sup_le hcomm hfixed) (hspan hz)
  have he' : w = z := Subtype.ext he
  exact he' ▸ hw

private theorem indexTwo_coatom {G : Type*} [Group G] {H : Subgroup G}
    (hi : H.index = 2) : IsCoatom H := by
  refine ⟨fun ht => by simp [ht] at hi, fun B hHB => ?_⟩
  have hm := relIndex_mul_index hHB.le
  rw [hi] at hm
  have hp : (H.relIndex B * B.index).Prime := hm ▸ Nat.prime_two
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hB⟩ | ⟨_, hrel⟩
  · exact index_eq_one.mp hB
  · exact (hHB.not_ge (relIndex_eq_one.mp hrel)).elim

private theorem binary_eq_of_ker_eq {G : Type*} [Group G]
    (f h : G →* Multiplicative (ZMod 2)) (he : f.ker = h.ker) : f = h := by
  ext x
  by_cases hx : f x = 1
  · have hx' : x ∈ f.ker := hx
    rw [he] at hx'
    exact hx.trans (MonoidHom.mem_ker.mp hx').symm
  · have hhx : h x ≠ 1 := by
      intro hh
      apply hx
      have hh' : x ∈ h.ker := hh
      rw [← he] at hh'
      exact hh'
    have hh : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a = b := by decide
    exact hh _ _ hx hhx

private theorem edgeCharacters_eq_of_nontrivial_subgroup {a t : Vertex R}
    (hi : (Z R t).relIndex (Z R a) = 2)
    (D : Subgroup (Z R a →* Multiplicative (ZMod 2)))
    (hD : D ≤ edgeCharacters a t) (hne : D ≠ ⊥) : D = edgeCharacters a t := by
  obtain ⟨f,hf,hf1⟩ := D.bot_or_exists_ne_one.resolve_left hne
  let T := (Z R t).subgroupOf (Z R a)
  have hco : IsCoatom T := indexTwo_coatom hi
  have hker : ∀ h ∈ edgeCharacters a t, h ≠ 1 → h.ker = T := by
    intro h hh hh1
    have hle : T ≤ h.ker := fun z hz => hh z hz
    rcases eq_or_lt_of_le hle with he | he
    · exact he.symm
    · have htop := hco.2 h.ker he
      exact (hh1 (MonoidHom.ker_eq_top_iff.mp htop)).elim
  apply le_antisymm hD
  intro h hh
  by_cases hh1 : h = 1
  · simpa only [hh1] using D.one_mem
  have he := binary_eq_of_ker_eq h f ((hker h hh hh1).trans (hker f (hD hf) hf1).symm)
  exact he ▸ hf



/-- Three group-theoretic source obligations for the edge character comparison.
They contain no character maps, product-case conclusion or (4.5.5) bound.
Their construction remains a separate obligation of this task. -/
structure EdgeDisplacements (p : Higher.SourcePath (alpha R)) : Prop where
  edge_span : Z R (p.walk.getVert 5) ≤
    ⁅Z R (alpha R), Q R (p.walk.getVert 5)⁆ ⊔ fixedSummand (R := R)
  first_movement : ⁅Z R (p.walk.getVert 6), Q R (p.walk.getVert 5)⁆ ≤ Z R (alpha R)
  second_movement : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
    Q R (p.walk.getVert 5)⁆ ≤ hatV R (alpha R) (p.walk.getVert 6)

include common in
private theorem EdgeDisplacements.transport {p : Higher.SourcePath (alpha R)}
    (h : EdgeDisplacements p) (g : stabilizer R (alpha R)) :
    Z R (act R g (p.walk.getVert 5)) ≤
      ⁅Z R (alpha R), Q R (act R g (p.walk.getVert 5))⁆ ⊔ fixedSummand (R := R) ∧
    ⁅Z R (act R g (p.walk.getVert 6)), Q R (act R g (p.walk.getVert 5))⁆ ≤ Z R (alpha R) ∧
    ⁅hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)),
      Q R (act R g (p.walk.getVert 5))⁆ ≤ hatV R (alpha R) (p.walk.getVert 6) := by
  let f := (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom
  have hZ : (Z R (alpha R)).map f = Z R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized R _ ((stabilizer R (alpha R)).inv_mem g.property))
  have hF : (fixedSummand (R := R)).map f = fixedSummand (R := R) :=
    mem_normalizer_iff_map_conj_eq.mp
      (fixedSummand_normalized common ((stabilizer R (alpha R)).inv_mem g.property))
  have hV : (hatV R (alpha R) (p.walk.getVert 6)).map f =
      hatV R (alpha R) (p.walk.getVert 6) :=
    mem_normalizer_iff_map_conj_eq.mp
      (hatV_normalized R _ _ ((stabilizer R (alpha R)).inv_mem g.property))
  have hcd : (hatV R (p.walk.getVert 6) (p.walk.getVert 8)).map f =
      hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) :=
    rightConjugate_hatV _ _ _
  have h5Z : (Z R (p.walk.getVert 5)).map f = Z R (act R g (p.walk.getVert 5)) :=
    (Z_act R g _).symm
  have h6Z : (Z R (p.walk.getVert 6)).map f = Z R (act R g (p.walk.getVert 6)) :=
    (Z_act R g _).symm
  have h5Q : (Q R (p.walk.getVert 5)).map f = Q R (act R g (p.walk.getVert 5)) :=
    (Q_act R g _).symm
  refine ⟨?_,?_,?_⟩
  · have hh := map_mono (f := f) h.edge_span
    simpa only [Subgroup.map_sup, map_commutator, hZ, hF, h5Z, h5Q] using hh
  · have hh := map_mono (f := f) h.first_movement
    simpa only [map_commutator, hZ, h6Z, h5Q] using hh
  · have hh := map_mono (f := f) h.second_movement
    simpa only [map_commutator, hV, hcd, h5Q] using hh

private theorem edge_adjacent (p : Higher.SourcePath (alpha R)) :
    Adjacent R (alpha R) (p.walk.getVert 5) := by
  have h := (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 4)
    (by rw [p.length_eq]; decide))
  simpa only [p.center_eq] using h

private theorem conjugate_edge_adjacent (p : Higher.SourcePath (alpha R))
    (g : stabilizer R (alpha R)) : Adjacent R (alpha R) (act R g (p.walk.getVert 5)) := by
  simpa only [show act R g (alpha R) = alpha R from g.property] using
    (adjacent_act_iff R g _ _).mpr (edge_adjacent p)

private theorem conjugate_edge_kernel_le (p : Higher.SourcePath (alpha R))
    (g : stabilizer R (alpha R)) : Q R (act R g (p.walk.getVert 5)) ≤ Mbar R := by
  intro x hx
  have h := hx.2 (alpha R) (adjacent_symm R (conjugate_edge_adjacent p g))
  simpa only [alpha, stabilizer_m_base] using h

private theorem conjugate_seed_le (p : Higher.SourcePath (alpha R))
    (g : stabilizer R (alpha R)) :
    Z R (act R g (p.walk.getVert 6)) ≤ hatV R (alpha R) (p.walk.getVert 6) := by
  rw [Z_act, hatV_eq_conjugatesIn]
  exact le_iSup (fun k : stabilizer R (alpha R) =>
    NormalizerTransfer.rightConjugate (Z R (p.walk.getVert 6)) k) g

private theorem first_seed_image_ne_bot (p : Higher.SourcePath (alpha R))
    (s : MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (g : stabilizer R (alpha R)) :
    ((Z R (act R g (p.walk.getVert 6))).subgroupOf
      (hatV R (alpha R) (p.walk.getVert 6))).map (firstMap common s) ≠ ⊥ := by
  intro hbot
  have hZg : Z R (act R g (p.walk.getVert 6)) ≤ Z R (alpha R) := by
    intro z hz
    let z₀ : hatV R (alpha R) (p.walk.getVert 6) := ⟨z,conjugate_seed_le p g hz⟩
    have hh : firstMap common s z₀ ∈
        ((Z R (act R g (p.walk.getVert 6))).subgroupOf
          (hatV R (alpha R) (p.walk.getVert 6))).map (firstMap common s) := ⟨z₀,hz,rfl⟩
    rw [hbot] at hh
    have hk : z₀ ∈ (firstMap common s).ker := hh
    rw [firstMap_kernel] at hk
    exact hk
  have hZ : Z R (p.walk.getVert 6) ≤ Z R (alpha R) := by
    intro z hz
    have hz' : (MulAut.conj (g : FreeAmalgam R)⁻¹) z ∈ Z R (act R g (p.walk.getVert 6)) := by
      rw [Z_act]
      exact mem_map_of_mem _ hz
    have hh := le_normalizer_iff.mp (Z_normalized R (alpha R)) g g.property _ (hZg hz')
    simpa only [MulAut.conj_apply, inv_inv, mul_assoc, mul_inv_cancel_left,
      inv_mul_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using hh
  have hV : hatV R (alpha R) (p.walk.getVert 6) ≤ Z R (alpha R) := by
    rw [hatV_eq_conjugatesIn]
    apply iSup_le
    intro k
    exact (map_mono hZ).trans
      (mem_normalizer_iff_map_conj_eq.mp
        (Z_normalized R _ ((stabilizer R (alpha R)).inv_mem k.property))).le
  obtain ⟨x,hx⟩ := s.onto (Multiplicative.ofAdd (fun _ : Fin 3 => (1 : ZMod 2)))
  have hk : x ∈ s.quotient.ker := s.kernel.symm ▸ hV x.property
  have hh := congrArg (fun v : Multiplicative W => v.toAdd 0)
    (hx.symm.trans (MonoidHom.mem_ker.mp hk))
  exact one_ne_zero hh



/-- The first edge image requires only the edge span and first displacement;
it is independent of the second-layer displacement. -/
theorem firstMap_edge_of_local_bounds (p : Higher.SourcePath (alpha R))
    (earlier : Earlier R geometry)
    (s : MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (g : stabilizer R (alpha R))
    (hspan : Z R (act R g (p.walk.getVert 5)) ≤
      ⁅Z R (alpha R), Q R (act R g (p.walk.getVert 5))⁆ ⊔ fixedSummand (R := R))
    (hmove : ⁅Z R (act R g (p.walk.getVert 6)),
      Q R (act R g (p.walk.getVert 5))⁆ ≤ Z R (alpha R)) :
    ((Z R (act R g (p.walk.getVert 6))).subgroupOf
      (hatV R (alpha R) (p.walk.getVert 6))).map (firstMap common s) =
        edgeCharacters (alpha R) (act R g (p.walk.getVert 5)) := by
  apply edgeCharacters_eq_of_nontrivial_subgroup
    (earlier.edge_Z_index _ _ rfl (conjugate_edge_adjacent p g))
  · rintro _ ⟨x,hx,rfl⟩
    exact characterMap_edge_of_displacement (firstMap common s) s.normalized
      (firstMap_kernel common s).symm.le
      (firstMap_on_fixed common s)
      (firstMap_action common s) (conjugate_edge_kernel_le p g) hmove hspan x hx
  · exact first_seed_image_ne_bot common p s g

/-- Construct the actual character comparisons from local displacement bounds.
The remaining source work is precisely the construction of EdgeDisplacements. -/
noncomputable def comparisonsOfDisplacements (p : Higher.SourcePath (alpha R))
    (earlier : Earlier R geometry)
    (s : MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (t : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (h : EdgeDisplacements p) : CharacterComparisons p := by
  refine { first := firstMap common s
           first_kernel := firstMap_kernel common s
           second := secondMap common t
           second_kernel := secondMap_kernel common t
           first_edge := ?_
           second_edge := ?_ }
  · intro g
    have hg := h.transport common g
    exact firstMap_edge_of_local_bounds common p earlier s g hg.1 hg.2.1
  · intro g x hx
    have hg := h.transport common g
    let f₁ := (MonoidHom.fst _ _).comp (secondMap common t)
    let f₂ := (MonoidHom.snd _ _).comp (secondMap common t)
    have h₁ : (hatV R (alpha R) (p.walk.getVert 6)).subgroupOf
        (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) ≤ f₁.ker := by
      intro y hy
      have hh : secondMap common t y = 1 :=
        MonoidHom.mem_ker.mp ((secondMap_kernel common t).symm ▸ hy)
      exact congrArg Prod.fst hh
    have h₂ : (hatV R (alpha R) (p.walk.getVert 6)).subgroupOf
        (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) ≤ f₂.ker := by
      intro y hy
      have hh : secondMap common t y = 1 :=
        MonoidHom.mem_ker.mp ((secondMap_kernel common t).symm ▸ hy)
      exact congrArg Prod.snd hh
    constructor
    · exact characterMap_edge_of_displacement f₁ t.normalized h₁
        (fun y z hz => (secondMap_on_fixed common t y z hz).1)
        (fun m u v z w hv hw => (secondMap_action common t m u v z w hv hw).1)
        (conjugate_edge_kernel_le p g) hg.2.2 hg.1 x hx
    · exact characterMap_edge_of_displacement f₂ t.normalized h₂
        (fun y z hz => (secondMap_on_fixed common t y z hz).2)
        (fun m u v z w hv hw => (secondMap_action common t m u v z w hv hw).2)
        (conjugate_edge_kernel_le p g) hg.2.2 hg.1 x hx

/-- Existence of both comparisons, conditional on the three explicit source bounds. -/
theorem characterComparisons_of_displacements (p : Higher.SourcePath (alpha R))
    (earlier : Earlier R geometry)
    (s : MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (t : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (h : EdgeDisplacements p) : Nonempty (CharacterComparisons p) :=
  ⟨comparisonsOfDisplacements common p earlier s t h⟩

/-- The constructed comparisons feed the literal equal-Z ordered-product consumer. -/
theorem equal_Z_span_of_displacements (p : Higher.SourcePath (alpha R))
    (earlier : Earlier R geometry)
    (s : MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (t : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (h : EdgeDisplacements p) (g : stabilizer R (alpha R))
    (heq : Z R (p.walk.getVert 5) = Z R (act R g (p.walk.getVert 5))) :
    (Z R (p.walk.getVert 6) : Set (FreeAmalgam R)) ⊆
      (Z R (alpha R) : Set (FreeAmalgam R)) *
        (Z R (act R g (p.walk.getVert 6)) : Set (FreeAmalgam R)) :=
  equal_Z_span_of_characters p (comparisonsOfDisplacements common p earlier s t h) g heq

/-- The constructed comparisons feed the distinct-Z product-intersection consumer. -/
theorem unequal_Z_intersection_of_displacements [Finite M] (p : Higher.SourcePath (alpha R))
    (earlier : Earlier R geometry)
    (s : MarkedDualSection source common (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (t : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (h : EdgeDisplacements p) (g : stabilizer R (alpha R))
    (hne : Z R (p.walk.getVert 5) ≠ Z R (act R g (p.walk.getVert 5))) :
    ((hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R))) ∩
    ((hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) : Set (FreeAmalgam R)) *
      (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R))) =
    (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) :=
  unequal_Z_intersection_of_characters earlier p
    (comparisonsOfDisplacements common p earlier s t h) g hne

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings

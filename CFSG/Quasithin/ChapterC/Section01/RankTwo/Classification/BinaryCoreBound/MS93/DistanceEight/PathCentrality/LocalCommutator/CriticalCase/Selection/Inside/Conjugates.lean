module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.InsidePreparation

/-!
# The quotient point and escaping conjugates in MS93 (4.4.1)(2)

For x in the local stabilizer G_c, K_0 is the literal preimage of the
centralizer of xD_c in G_c/D_c, and K is its normalizer inside G_c. We
construct W_0 = <Z_a^K> and W from its G_c-conjugates for which Z_e is not
contained in K^g, using right conjugation throughout.

If W is not contained in a subgroup Y, one of its Z_a-generators escapes Y.
The K-conjugator used to obtain that generator preserves K^g. Centralizing
the corresponding displacement would put Z_e inside the same K^g, so the
selected generator has nontrivial triple commutator as well. The critical
path application retains this single conjugator for both conclusions.

The source displacement point is chosen with [x,Q_a] = 1. Its inclusion
in Z_c D_c is the separate dual-module argument, not asserted here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), claim (2), printed p.891; (1.5), pp.843--845.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside
variable {M : Type*} [Group M] {R : Subgroup M}

/-- The source centralizer, pulled back from the literal local quotient by D_c. -/
noncomputable def pointCentralizer (c : Vertex R) (x : stabilizer R c) :
    Subgroup (FreeAmalgam R) := by
  let := PathCentrality.fixedCore_normal R c
  let π := QuotientGroup.mk' ((fixedCore R c).subgroupOf (stabilizer R c))
  exact ((centralizer ({π x} : Set _)).comap π).map (stabilizer R c).subtype

/-- The normalizer is taken inside G_c. -/
noncomputable def pointNormalizer (c : Vertex R) (x : stabilizer R c) :
    Subgroup (FreeAmalgam R) :=
  stabilizer R c ⊓ normalizer (pointCentralizer c x : Set (FreeAmalgam R))

/-- The source W_0, with right conjugation by the actual local normalizer. -/
noncomputable def normalizerSpan (a c : Vertex R) (x : stabilizer R c) :
    Subgroup (FreeAmalgam R) :=
  NormalizerTransfer.conjugatesIn (Z R a) (pointNormalizer c x)

/-- The source W. The escape test is T not contained in K^g, not W_0^g not contained in K. -/
noncomputable def escapingSpan (a c e : Vertex R) (x : stabilizer R c) :
    Subgroup (FreeAmalgam R) :=
  ⨆ g : stabilizer R c,
    ⨆ (_ : ¬ Z R e ≤ NormalizerTransfer.rightConjugate (pointNormalizer c x) g),
      NormalizerTransfer.rightConjugate (normalizerSpan a c x) g

private theorem rightConjugate_mul {G : Type*} [Group G]
    (A : Subgroup G) (g h : G) :
    NormalizerTransfer.rightConjugate (NormalizerTransfer.rightConjugate A g) h =
      NormalizerTransfer.rightConjugate A (g * h) := by
  simp only [NormalizerTransfer.rightConjugate, map_map]
  congr 1
  ext y
  simp [mul_assoc]

theorem pointCentralizer_le_stabilizer (c : Vertex R) (x : stabilizer R c) :
    pointCentralizer c x ≤ stabilizer R c := by
  rintro y ⟨z, hz, rfl⟩
  exact z.property

theorem pointCentralizer_le_pointNormalizer (c : Vertex R) (x : stabilizer R c) :
    pointCentralizer c x ≤ pointNormalizer c x :=
  le_inf (pointCentralizer_le_stabilizer c x) (pointCentralizer c x).le_normalizer

theorem local_centralizer_le_pointCentralizer (c : Vertex R) (x : stabilizer R c) :
    stabilizer R c ⊓ centralizer ({(x : FreeAmalgam R)} : Set _) ≤ pointCentralizer c x := by
  intro y hy
  let := PathCentrality.fixedCore_normal R c
  let π := QuotientGroup.mk' ((fixedCore R c).subgroupOf (stabilizer R c))
  refine ⟨⟨y, hy.1⟩, ?_, rfl⟩
  change π ⟨y, hy.1⟩ ∈ centralizer ({π x} : Set _)
  apply mem_centralizer_singleton_iff.mpr
  have h : (⟨y, hy.1⟩ : stabilizer R c) * x = x * ⟨y, hy.1⟩ :=
    Subtype.ext (mem_centralizer_singleton_iff.mp hy.2)
  simpa only [map_mul] using congrArg π h

/-- Membership uses the marked element of G_c/D_c and its actual quotient map. -/
theorem mem_pointCentralizer_iff (c : Vertex R) (x y : stabilizer R c) :
    (y : FreeAmalgam R) ∈ pointCentralizer c x ↔
      letI := PathCentrality.fixedCore_normal R c
      let π := QuotientGroup.mk' ((fixedCore R c).subgroupOf (stabilizer R c))
      π y * π x = π x * π y := by
  let := PathCentrality.fixedCore_normal R c
  change (y : FreeAmalgam R) ∈
    ((centralizer ({QuotientGroup.mk' _ x} : Set _)).comap (QuotientGroup.mk' _)).map
      (stabilizer R c).subtype ↔ _
  constructor
  · rintro ⟨z, hz, he⟩
    have hzy : z = y := Subtype.ext he
    subst z
    exact mem_centralizer_singleton_iff.mp hz
  · intro h
    exact ⟨y, mem_centralizer_singleton_iff.mpr h, rfl⟩

/-- The fixed core is contained in the literal quotient-centralizer preimage. -/
theorem fixedCore_le_pointCentralizer (c : Vertex R) (x : stabilizer R c) :
    fixedCore R c ≤ pointCentralizer c x := by
  intro y hy
  let yS : stabilizer R c := ⟨y, hy.1.1⟩
  change (yS : FreeAmalgam R) ∈ pointCentralizer c x
  rw [mem_pointCentralizer_iff]
  let := PathCentrality.fixedCore_normal R c
  have he : QuotientGroup.mk' ((fixedCore R c).subgroupOf (stabilizer R c)) yS = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hy
  simp only [he, one_mul, mul_one]

/-- The quotient point is nonidentity exactly when the original element escapes D_c. -/
theorem quotient_point_ne_one (c : Vertex R) (x : stabilizer R c)
    (hx : (x : FreeAmalgam R) ∉ fixedCore R c) :
    letI := PathCentrality.fixedCore_normal R c
    QuotientGroup.mk' ((fixedCore R c).subgroupOf (stabilizer R c)) x ≠ 1 := by
  let := PathCentrality.fixedCore_normal R c
  exact fun h => hx ((QuotientGroup.eq_one_iff x).mp h)

/-- W_0 is invariant under its specified local normalizer. -/
theorem normalizerSpan_normalized (a c : Vertex R) (x : stabilizer R c) :
    pointNormalizer c x ≤ normalizer (normalizerSpan a c x : Set (FreeAmalgam R)) :=
  NormalizerTransfer.conjugatesIn_normalized _ _

/-- The intermediate K-span stays in the original G_c-span. -/
theorem normalizerSpan_le_localZSpan (a c : Vertex R) (x : stabilizer R c) :
    normalizerSpan a c x ≤ localZSpan R a c := by
  apply iSup_le
  intro k
  change (Z R a).map (MulAut.conj (k : FreeAmalgam R)⁻¹).toMonoidHom ≤ _
  rw [← Z_act]
  exact le_iSup_of_le (⟨k, k.property.1⟩ : stabilizer R c) le_rfl

/-- Taking all G_c-conjugates of W_0 recovers exactly the source module. -/
theorem normalizerSpan_conjugates_eq (a c : Vertex R) (x : stabilizer R c) :
    NormalizerTransfer.conjugatesIn (normalizerSpan a c x) (stabilizer R c) =
      localZSpan R a c := by
  apply le_antisymm
  · apply iSup_le
    intro g
    have hn := mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized R a c ((stabilizer R c).inv_mem g.property))
    exact (map_mono (normalizerSpan_le_localZSpan a c x)).trans hn.le
  · rw [localZSpan_eq_conjugates]
    apply iSup_mono
    intro g
    exact map_mono (Escape.Initial.Natural.conjugatesIn_contains _ _)

/-- Keeping just the escaping conjugates produces a subgroup of the same source module. -/
theorem escapingSpan_le_localZSpan (a c e : Vertex R) (x : stabilizer R c) :
    escapingSpan a c e x ≤ localZSpan R a c := by
  apply iSup_le
  intro g
  apply iSup_le
  intro _
  rw [← normalizerSpan_conjugates_eq a c x]
  exact le_iSup_of_le g le_rfl

/-- The endpoint actor normalizes the escaping span: right conjugation
permutes precisely the conjugates satisfying the same escape test. -/
theorem escapingSpan_normalized (a c e : Vertex R) (x : stabilizer R c)
    (he : Z R e ≤ stabilizer R c) :
    Z R e ≤ normalizer (escapingSpan a c e x : Set (FreeAmalgam R)) := by
  apply le_normalizer_iff.mpr
  intro z hz y hy
  have hm : (escapingSpan a c e x).map (MulAut.conj z).toMonoidHom ≤ escapingSpan a c e x := by
    simp only [escapingSpan, Subgroup.map_iSup]
    apply iSup_le
    intro g
    apply iSup_le
    intro hescape
    rw [← inv_inv z]
    change NormalizerTransfer.rightConjugate
      (NormalizerTransfer.rightConjugate (normalizerSpan a c x) g) z⁻¹ ≤ _
    rw [rightConjugate_mul]
    have hescape' : ¬ Z R e ≤
        NormalizerTransfer.rightConjugate (pointNormalizer c x) ((g : FreeAmalgam R) * z⁻¹) := by
      intro hh
      have hh' := map_mono (f := (MulAut.conj z⁻¹).toMonoidHom) hh
      change NormalizerTransfer.rightConjugate (Z R e) z ≤
        NormalizerTransfer.rightConjugate
          (NormalizerTransfer.rightConjugate (pointNormalizer c x) ((g : FreeAmalgam R) * z⁻¹)) z at hh'
      rw [rightConjugate_mul, inv_mul_cancel_right] at hh'
      have hzZ : NormalizerTransfer.rightConjugate (Z R e) z = Z R e :=
        mem_normalizer_iff_map_conj_eq.mp ((Z R e).le_normalizer ((Z R e).inv_mem hz))
      exact hescape (hzZ ▸ hh')
    exact le_iSup_of_le
      (⟨(g : FreeAmalgam R) * z⁻¹,
        (stabilizer R c).mul_mem g.property ((stabilizer R c).inv_mem (he hz))⟩ : stabilizer R c)
      (le_iSup_of_le hescape' le_rfl)
  exact hm (mem_map_of_mem (MulAut.conj z).toMonoidHom hy)

private theorem conjugate_pointNormalizer_contains_centralizer
    (c : Vertex R) (x : stabilizer R c) {g : FreeAmalgam R}
    (hg : g ∈ stabilizer R c) :
    stabilizer R c ⊓ centralizer
        ({MulAut.conj g⁻¹ (x : FreeAmalgam R)} : Set _) ≤
      NormalizerTransfer.rightConjugate (pointNormalizer c x) g := by
  intro y hy
  have ht : MulAut.conj g y ∈ pointNormalizer c x := by
    apply pointCentralizer_le_pointNormalizer c x
    apply local_centralizer_le_pointCentralizer c x
    refine ⟨(stabilizer R c).mul_mem ((stabilizer R c).mul_mem hg hy.1)
      ((stabilizer R c).inv_mem hg), ?_⟩
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp hy.2)
    simpa [MulAut.conj_apply, mul_assoc] using h
  refine ⟨MulAut.conj g y, ht, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

/-- Escaping the point normalizer forces a nontrivial triple on the same conjugate. -/
theorem triple_ne_of_escape {a c e : Vertex R} (x : stabilizer R c)
    (hx : (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆)
    (he : Z R e ≤ stabilizer R c) {g : FreeAmalgam R}
    (hg : g ∈ stabilizer R c)
    (hescape : ¬ Z R e ≤ NormalizerTransfer.rightConjugate (pointNormalizer c x) g) :
    ⁅⁅Z R (act R g a), Q R c⁆, Z R e⁆ ≠ ⊥ := by
  intro htriple
  apply hescape
  apply le_trans (le_inf he ?_) (conjugate_pointNormalizer_contains_centralizer c x hg)
  have hQ : (Q R c).map (MulAut.conj g⁻¹).toMonoidHom = Q R c :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R c ((stabilizer R c).inv_mem hg))
  have hxg : MulAut.conj g⁻¹ (x : FreeAmalgam R) ∈ ⁅Z R (act R g a), Q R c⁆ := by
    have hh := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hx
    rwa [map_commutator, hQ, ← Z_act] at hh
  have hcomm := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp htriple)
  intro y hy
  exact mem_centralizer_singleton_iff.mpr ((hcomm hy) _ hxg).symm

/-- Failure of containment of W selects a generator of W_0^g, preserving
both the escape test and the original G_c-orbit. -/
theorem exists_conjugate_of_escaping_not_le {a c e : Vertex R}
    (x : stabilizer R c) (Y : Subgroup (FreeAmalgam R))
    (hW : ¬ escapingSpan a c e x ≤ Y) :
    ∃ g ∈ stabilizer R c,
      ¬ Z R (act R g a) ≤ Y ∧
      ¬ Z R e ≤ NormalizerTransfer.rightConjugate (pointNormalizer c x) g := by
  classical
  by_contra! h
  apply hW
  apply iSup_le
  intro g
  apply iSup_le
  intro hescape
  simp only [normalizerSpan, NormalizerTransfer.conjugatesIn,
    NormalizerTransfer.rightConjugate, Subgroup.map_iSup]
  apply iSup_le
  intro k
  change NormalizerTransfer.rightConjugate
    (NormalizerTransfer.rightConjugate (Z R a) k) g ≤ Y
  rw [rightConjugate_mul, NormalizerTransfer.rightConjugate, ← Z_act]
  by_contra hZY
  have he := h ((k : FreeAmalgam R) * g)
    ((stabilizer R c).mul_mem k.property.1 g.property) hZY
  apply hescape
  have heq : NormalizerTransfer.rightConjugate (pointNormalizer c x) k = pointNormalizer c x :=
    mem_normalizer_iff_map_conj_eq.mp ((pointNormalizer c x).le_normalizer
      ((pointNormalizer c x).inv_mem k.property))
  rwa [← rightConjugate_mul, heq] at he

variable {L : Subgroup M} {source : LocalSource L R} {geometry : Geometry R}

/-- Once the dual-module step places x in Z_c D_c, the whole local
kernel belongs to K_0, with the same literal quotient marking. -/
theorem kernel_le_pointCentralizer_of_mem_Z_join_fixedCore [Finite M]
    {c : Vertex R} (hc : color R c = false) (x : stabilizer R c)
    (hx : (x : FreeAmalgam R) ∈ Z R c ⊔ fixedCore R c) :
    Q R c ≤ pointCentralizer c x := by
  let := PathCentrality.fixedCore_normal R c
  let π := QuotientGroup.mk' ((fixedCore R c).subgroupOf (stabilizer R c))
  have hp : (x : FreeAmalgam R) ∈
      (Z R c : Set (FreeAmalgam R)) * (fixedCore R c : Set (FreeAmalgam R)) := by
    rw [← join_fixedCore_eq_mul R (Z R c) (Z_le_stabilizer R c)]
    exact hx
  obtain ⟨z, hz, d, hd, hzd⟩ := hp
  let zS : stabilizer R c := ⟨z, Z_le_stabilizer R c hz⟩
  let dS : stabilizer R c := ⟨d, hd.1.1⟩
  have hxd : zS * dS = x := Subtype.ext hzd
  have hdπ : π dS = 1 := (QuotientGroup.eq_one_iff dS).mpr hd
  have hxπ : π x = π zS := by rw [← hxd, map_mul, hdπ, mul_one]
  intro y hy
  let yS : stabilizer R c := ⟨y, hy.1⟩
  change (yS : FreeAmalgam R) ∈ pointCentralizer c x
  rw [mem_pointCentralizer_iff]
  change π yS * π x = π x * π yS
  rw [hxπ]
  have hcomm : yS * zS = zS * yS := Subtype.ext
    ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R c hc)) hz y hy)
  simpa only [map_mul] using congrArg π hcomm

/-- Choose the actual displacement point and prove the commuting premise of
(1.5) before invoking any representation-theoretic conclusion. -/
theorem exists_displacement_point [Finite M] (common : CommonFacts R source geometry)
    {a c : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hB : ⁅Z R a, Q R c⁆ ≤ B R c (geometry.Z_normal c))
    (hn : ¬ ⁅Z R a, Q R c⁆ ≤ fixedCore R c) :
    ∃ x : stabilizer R c,
      (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆ ∧
      (x : FreeAmalgam R) ∉ fixedCore R c ∧
      (x : FreeAmalgam R) ∈ B R c (geometry.Z_normal c) ∧
      (x : FreeAmalgam R) ∈ Z R a ∧
      ⁅zpowers (x : FreeAmalgam R), Q R a⁆ = ⊥ := by
  classical
  obtain ⟨x, hx, hnot⟩ := Set.not_subset.mp hn
  have hxZ := (displacement_le_U common ha hd).trans (U_le_Z R a) hx
  have hxS := ((Z_le_localZSpan R a c).trans
    ((localZSpan_le_Q R hc hd.le common.large_distance).trans (fun _ hy => hy.1))) hxZ
  refine ⟨⟨x, hxS⟩, hx, hnot, hB hx, hxZ, ?_⟩
  exact le_bot_iff.mp ((commutator_mono (zpowers_le.mpr hxZ) le_rfl).trans
    (geometry.centralizes a ha).le)

/-- The noncontained escaping span supplies both required conclusions for
one conjugator on the given critical path. -/
theorem exists_conjugate_of_escaping_span {a c e : Vertex R}
    (p : CriticalPath R geometry c e) (hb : 2 < geometry.b R)
    (x : stabilizer R c) (hx : (x : FreeAmalgam R) ∈ ⁅Z R a, Q R c⁆)
    (hW : ¬ escapingSpan a c e x ≤ Q R (p.walk.getVert (p.walk.length - 2))) :
    ∃ g ∈ stabilizer R c,
      ¬ Z R (act R g a) ≤ Q R (p.walk.getVert (p.walk.length - 2)) ∧
      ⁅⁅Z R (act R g a), Q R c⁆, Z R e⁆ ≠ ⊥ := by
  obtain ⟨g, hg, hcrit, hescape⟩ := exists_conjugate_of_escaping_not_le x _ hW
  exact ⟨g, hg, hcrit,
    triple_ne_of_escape x hx (p.endpoint_Z_le_start_stabilizer (by omega)) hg hescape⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside

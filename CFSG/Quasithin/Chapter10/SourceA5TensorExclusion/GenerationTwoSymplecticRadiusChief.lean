module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRadiusFour
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalChiefBudget
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalCriticalResidual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusEdge
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.NoncentralPair

/-!
# The original radius chief factor and its large-image centrality

A large critical image supplies an elementary actor of order sixteen in the
literal residual preimage. The penultimate full radius kernel gives fixed
index at most sixty-four on the quotient by the full starting seed. Applying
the chief budget in that preimage and mapping back gives the residual
fixed-or-covering alternative on the original group, including when the
ambient quotient has outer automorphisms. Abelian edge generation then
centralizes [V,Q] in V and yields the original derived and triple bounds.

The final application keeps the surviving obstruction precise: failure of
radius centrality forces every critical image to have order four, proves
X=Z at both endpoints, and selects an actual noncentral critical pair through
the radius. That small-image case and the terminal distance-four exclusion
remain required; no whole-core or plane recognition is asserted here.

Source: MS93 (5.2)(i)--(iii), printed pp.914--915, on the original group of
Aschbacher--Smith 9.3.10, printed p.734. The two tensor assemblies remain the
final consumers of this source branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- The literal radius quotient has the residual fixed-or-covering alternative. -/
theorem original_large_critical_radius_residual_dichotomy
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {z : Vertex R} (_path : CriticalPath R geometry (alpha R) z),
      16 ≤ (Q R z).relIndex (Z R (alpha R)) →
      ∀ X₀ : Subgroup c.M, X₀.Normal → X₀ ≤ (V R (alpha R)).comap (embedM R) →
      ⁅X₀,pResidual 2 c.M⁆ ≤ (Z R (alpha R)).comap (embedM R) ∨
        ⁅(V R (alpha R)).comap (embedM R),pResidual 2 c.M⁆ ≤
          X₀ ⊔ (Z R (alpha R)).comap (embedM R) := by
  intro R geometry z path hlarge X₀ hXN hXV
  let := hXN
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have hb : 4 ≤ geometry.b R := c.original_geometry_four_le eK geometry
  let f := embedM R
  let V₀ := (V R (alpha R)).comap f
  let Z₀ := (Z R (alpha R)).comap f
  let A := (Z R z).comap f
  let P := (Q R (path.walk.getVert (path.walk.length-2))).comap f
  let := ChapterC.NaturalSixControl.SymplecticSetup.Source.radius_comap_normal (R := R)
  let := ChapterC.NaturalSixControl.SymplecticSeed.Z_comap_normal R
  have hAS : Z R z ≤ f.range :=
    (path.endpoint_Z_le_start_stabilizer (by omega)).trans_eq (stabilizer_m_base R)
  have hAm : A.map f = Z R z := map_comap_eq_self hAS
  have hVm : V₀.map f = V R (alpha R) :=
    map_comap_eq_self ((geometry.V_local _ rfl (by change 2 < geometry.b R; omega)).trans_eq (stabilizer_m_base R))
  have hZm : Z₀.map f = Z R (alpha R) :=
    map_comap_eq_self ((Z_le_stabilizer R _).trans_eq (stabilizer_m_base R))
  let := geometry.Z_elementary (by omega) z path.end_color
  let j : A →* Z R z := (f.comp A.subtype).codRestrict _ (fun x => x.property)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective j
    (fun x y he => Subtype.ext (embedM_injective R (congrArg Subtype.val he)))
  have hV : V₀ ≤ q.ker := by
    rw [QuotientGroup.ker_mk']
    have hh := comap_mono (f := f) (geometry.V_le_Q (by omega) (alpha R) rfl)
    rwa [Q_alpha_comap R hodd.isPGroup hodd.twoCore_le] at hh
  have hinner : A.map q ≤ (pResidual 2 c.M).map q := by
    apply map_le_iff_le_comap.mpr
    rw [comap_map_eq,QuotientGroup.ker_mk']
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [Subgroup.map_sup,hAm,←Ltilde_alpha,←Q_alpha R hodd.isPGroup hodd.twoCore_le]
    exact original_critical_seed_le_residual_sup_kernel R hms hodd.isPGroup hne
      hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      hcard hBC hsq (c.original_critical_reverse eK geometry (by change 0 < geometry.b R; omega) path) (by omega)
  have hlargeA : 4^2 ≤ q.ker.relIndex A := by
    rw [QuotientGroup.ker_mk',←relIndex_map_map_of_injective _ _ (embedM_injective R),
      ←Q_alpha R hodd.isPGroup hodd.twoCore_le,hAm]
    rcases c.original_critical_indices_four_or_sixteen eK geometry path with hs | hl
    · rw [hs.1] at hlarge
      omega
    · rw [hl.2]
      decide
  have hcomm : ⁅V₀ ⊓ P,A⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (embedM_injective R),hVm,hAm,hZm]
    exact (commutator_mono (inf_le_inf_left _ (map_comap_le _ _)) le_rfl).trans
      (c.original_radius_displacement_of_large_critical_index eK geometry path hlarge)
  have hindex : P.relIndex V₀ ≤ 4^3 := by
    rw [relIndex_comap,hVm]
    apply (c.original_radius_image_index_le_64_at_four eK geometry rfl ?_ ?_).1
    · apply (path.vertex_color (Nat.sub_le _ _)).mpr
      rw [path.length_eq_b,c.original_geometry_eq_four eK geometry]
      decide
    · rw [path.dist_start (Nat.sub_le _ _),path.length_eq_b]
      change geometry.b R - 2 + 2 ≤ geometry.b R
      omega
  have hF : Nat.card BinaryField.four.Carrier = 2^2 := BinaryField.four.card_eq
  have hc : Nat.card ((pResidual 2 c.M).map q) = Nat.card (Sp BinaryField.four.Carrier) := by
    rw [hcard,card_sp,hF]
    norm_num
  apply original_symplectic_residual_dichotomy_of_index hF (by decide) q
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    hc hsq V₀ Z₀ (comap_mono (Z_le_VBall R (alpha R) 2)) hV A hinner
    (by simpa only [hF,show (2:ℕ)^2=4 by decide] using hlargeA) P hcomm (by simpa only [hF,show (2:ℕ)^2=4 by decide] using hindex) X₀ hXV

/-- The chief budget gives centrality on the original radius in the large-image branch. -/
theorem original_radius_commutator_central_of_large_base_image
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {z : Vertex R} (_path : CriticalPath R geometry (alpha R) z),
      16 ≤ (Q R z).relIndex (Z R (alpha R)) →
      ∀ a : Vertex R, color R a = false →
        ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  intro R geometry z path hlarge a ha
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let V₀ := (V R (alpha R)).comap (embedM R)
  let := ChapterC.NaturalSixControl.SymplecticSetup.Source.radius_comap_normal (R := R)
  have hd := c.original_large_critical_radius_residual_dichotomy eK geometry path hlarge
    ⁅V₀,pCore 2 c.M⁆ inferInstance (commutator_le_left _ _)
  have hgen : pResidual 2 c.M ⊔ R = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 x
    exact Subgroup.mul_mem _ (mem_sup_left hk) (mem_sup_right hr)
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have hbase := ChapterC.RankTwo.NonbinarySymplectic.RadiusEdge.radius_commutator_central_of_preimage_dichotomy
    geometry hodd.isPGroup hodd.twoCore_le hgen hb hd
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have hV : V R (mVertex R g) = (V R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using V_act R g (alpha R)
  have hQ : Q R (mVertex R g) = (Q R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using Q_act R g (alpha R)
  rw [hV,hQ,←map_commutator]
  exact (map_mono hbase).trans (map_centralizer_le_centralizer_image _ _)

/-- A large image on any original critical path gives centrality at every
vertex, by the original graph action. -/
theorem original_radius_commutator_central_of_large_critical
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {u z : Vertex R} (_path : CriticalPath R geometry u z),
      16 ≤ (Q R z).relIndex (Z R u) →
      ∀ a : Vertex R, color R a = false →
        ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  intro R geometry u z path hlarge a ha
  obtain ⟨g,hug⟩ := exists_mVertex_of_color R path.start_color
  have hf : act R g⁻¹ u = alpha R := by
    rw [hug,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have hfcol : color R (act R g⁻¹ u) = false := by rw [hf]; rfl
  have hpair : CriticalPair R (alpha R) (act R g⁻¹ z)
      (geometry.exists_critical (alpha R) rfl) := by
    simpa only [hf] using (criticalPair_act_iff R g⁻¹ u z
      (geometry.exists_critical u path.start_color)
      (geometry.exists_critical (act R g⁻¹ u) hfcol)).mpr path.critical
  have hi : 16 ≤ (Q R (act R g⁻¹ z)).relIndex (Z R (alpha R)) := by
    rw [←hf,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hlarge
  exact c.original_radius_commutator_central_of_large_base_image eK geometry
    (CriticalPath.ofPair rfl hpair) hi a ha

/-- The actual distance-four derived-radius and triple-commutator conclusions
in the large-image branch, retaining the full original X and kernels. -/
theorem original_large_critical_radius_bounds
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {u z : Vertex R} (_path : CriticalPath R geometry u z),
      16 ≤ (Q R z).relIndex (Z R u) →
      ∀ a : Vertex R, color R a = false → ∀ d w : Vertex R,
        ⁅V R a,V R a⁆ ≤ X R a ∧
        ⁅⁅X R d ⊓ Q R a,V R a ⊓ Q R w⁆,V R a ⊓ Q R w⁆ = ⊥ := by
  intro R geometry u z path hlarge a ha d w
  have hc := c.original_radius_commutator_central_of_large_critical eK geometry path hlarge a ha
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  exact ⟨SectionFive.radius_derived_le_X R geometry hb ha hc,
    SectionFive.critical_radius_triple_commutator R hc⟩

/-- Any remaining failure of original radius centrality forces every
critical image to be a field-sized root and proves X=Z at its endpoints. -/
theorem original_noncentral_radius_small_critical_data
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a : Vertex R}, color R a = false →
      (¬ ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R))) →
      ∀ {u z : Vertex R} (_path : CriticalPath R geometry u z),
        (Q R z).relIndex (Z R u) = 4 ∧ (Q R u).relIndex (Z R z) = 4 ∧
        X R u = Z R u ∧ X R z = Z R z := by
  intro R geometry a ha hn u z path
  have hs : (Q R z).relIndex (Z R u) < 16 := by
    by_contra! hlarge
    exact hn (c.original_radius_commutator_central_of_large_critical eK geometry path hlarge a ha)
  obtain ⟨hu,hz,hXu⟩ := c.original_small_critical_data eK geometry path hs
  exact ⟨hu,hz,hXu,c.original_X_eq_Z_at_of_eq path.start_color path.end_color hXu⟩

/-- The surviving noncentral branch selects a literal two-step pair with
nontrivial mixed triple commutator; both original seed images are roots. -/
theorem original_noncentral_radius_root_pair
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a : Vertex R}, color R a = false →
      (¬ ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R))) →
      ∃ u z, (cosetGraph R).dist u a = 2 ∧ (cosetGraph R).dist z a = 2 ∧
        ⁅⁅Z R u,Q R a⁆,Z R z⁆ ≠ ⊥ ∧
        ∃ _path : CriticalPath R geometry u z,
          (Q R z).relIndex (Z R u) = 4 ∧ (Q R u).relIndex (Z R z) = 4 ∧
          X R u = Z R u ∧ X R z = Z R z := by
  intro R geometry a ha hn
  obtain ⟨u,z,_,_,hua,hza,htrip,hu,hcrit⟩ := SectionFive.exists_noncentral_critical_pair R
    geometry (c.original_geometry_eq_four eK geometry) a ha hn
  let path : CriticalPath R geometry u z := CriticalPath.ofPair hu hcrit
  exact ⟨u,z,hua,hza,htrip,path,
    c.original_noncentral_radius_small_critical_data eK geometry ha hn path⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup

module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.RadiusAction
public import Theory.SpecificGroups.SymplecticFour.NormalQuadraticElementary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootImage

/-!
# The full radius image at the distance-four boundary

Every radius seed is normalized by the radius. In the marked natural action,
a seed either vanishes or is an actual critical actor, and hence is quadratic.
The normal-quadratic Sylow theorem makes their complete image elementary.
The action kernel and natural quotient in the statement are the literal ones;
no characteristic replacement or abelianness of the radius is used.

The original tensor application is `GenerationTwoSymplecticRadiusFour`.
Source: Meierfrankenfeld--Stellmacher (1993), (5.2), printed p.914.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

variable {M F : Type*} [Group M] [Finite M] [Field F] [Finite F] [CharP F 2]
variable {R : Subgroup M} {geometry : Geometry R} {a z : Vertex R}

/-- The full radius image is elementary, including the distance-four boundary. -/
theorem radius_image_elementary_of_natural_action
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    (hb : 2 < geometry.b R) (hp : IsPGroup 2 (Q R a))
    (ha : color R a = false) (hd : (cosetGraph R).dist a z + 2 ≤ geometry.b R)
    (f : V R a →* Sp F) (hf : f.ker = (Q R z).subgroupOf (V R a))
    (π : U R z →* Multiplicative (Vector F)) (hπ : Function.Surjective π)
    (hact : ∀ (v : V R a) (u : U R z),
      π ⟨v.val*u.val*v.val⁻¹,
        (mem_normalizer_iff.mp (U_normalized z
          (radius_le_stabilizer_of_distance R geometry ha hd v.property)) u.val).mp u.property⟩ =
        Multiplicative.ofAdd (f v • (π u).toAdd)) :
    IsElementaryAbelian 2 f.range := by
  let W := V R a
  let I := {c : Vertex R // color R c = false ∧ (cosetGraph R).dist c a ≤ 2}
  have hgenV : V R a = ⨆ c : I, Z R c.val := by
    apply le_antisymm
    · apply (V_le_iff R ha _).mpr
      intro c hc hca
      exact le_iSup_of_le (⟨c,hc,hca⟩ : I) le_rfl
    · exact iSup_le fun c => le_iSup_of_le c.val (le_iSup_of_le c.property.2 le_rfl)
  have hseed (c : I) : Z R c.val ≤ V R a := hgenV ▸ le_iSup (fun c : I => Z R c.val) c
  let C (c : I) := (Z R c.val).subgroupOf W
  let A (c : I) := (C c).map f
  have hCm (c : I) : (C c).map W.subtype = Z R c.val := map_subgroupOf_eq_of_le (hseed c)
  have hgen₀ : (⊤ : Subgroup W) = ⨆ c : I, C c := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_iSup]
    simp only [hCm]
    rw [←MonoidHom.range_eq_map,range_subtype]
    exact hgenV
  have hgenP : f.range = ⨆ c : I, A c := by
    rw [MonoidHom.range_eq_map,hgen₀,Subgroup.map_iSup]
  have hP : IsPGroup 2 f.range :=
    (hp.to_le (geometry.V_le_Q hb a ha)).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have helem (c : I) : IsElementaryAbelian 2 (A c) := by
    let := geometry.Z_elementary (by omega) c.val c.property.1
    let := IsElementaryAbelian.subgroupOf (p := 2) (hseed c)
    exact IsElementaryAbelian.map f
  have hnorm (c : I) : f.range ≤ normalizer (A c : Set (Sp F)) := by
    have hn : V R a ≤ normalizer (Z R c.val : Set (FreeAmalgam R)) :=
      (geometry.V_le_Q hb a ha).trans
        ((Q_le_stabilizer_of_dist_le_two a c.val ha c.property.1
          (by rw [SimpleGraph.dist_comm]; exact c.property.2)).trans (Z_normalized R c.val))
    have htop : (⊤ : Subgroup W) ≤ normalizer (C c : Set W) := by
      intro x _
      exact ((comap_mono hn).trans (le_normalizer_comap W.subtype)) x.property
    rw [MonoidHom.range_eq_map]
    exact (map_mono htop).trans (le_normalizer_map f)
  have hquad (c : I) : ∀ x ∈ A c, ∀ y ∈ A c, ∀ v : Vector F,
      x • (y • v-v)=y • v-v := by
    let δ := f.comp (inclusion (hseed c))
    have he : δ.range = A c := by rw [MonoidHom.range_comp,inclusion_range]
    rw [←he]
    by_cases hCQ : Z R c.val ≤ Q R z
    · have hδ (x : Z R c.val) : δ x = 1 := by
        change inclusion (hseed c) x ∈ f.ker
        rw [hf]
        exact hCQ x.property
      rintro x ⟨x,rfl⟩ y ⟨y,rfl⟩ v
      simp only [hδ,one_smul]
    · have hdist : (cosetGraph R).dist c.val z ≤ geometry.b R := by
        have ht := (cosetGraph_connected R).dist_triangle (u := c.val) (v := a) (w := z)
        have hc := c.property.2
        omega
      have hcrit : CriticalPair R c.val z (geometry.exists_critical c.val c.property.1) := by
        refine ⟨le_antisymm ?_ (criticalDistance_le R c.val _ hCQ),hCQ⟩
        rwa [geometry.distance_constant c.val c.property.1]
      let path : CriticalPath R geometry c.val z := CriticalPath.ofPair c.property.1 hcrit
      apply NonbinarySymplectic.critical_quotient_actor_quadratic path (by omega) π hπ δ
      intro x u
      exact hact (inclusion (hseed c) x) u
  exact NormalQuadratic.generated_elementary hF hn f.range hP A hgenP helem hnorm hquad

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

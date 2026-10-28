module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.CriticalSeed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.StarGeometry
public import Theory.GroupTheory.CentralizerInjectiveImage
/-!
# Full-Sylow seed transport and the original star radius

The literal fixed seed is transported under both conjugators in the source
star. Each transported actor remains a full Sylow of its own component,
and its incident edge core still normalizes the seed. The critical-seed
bound therefore places the entire star in every core at distance at most
b minus two from alpha, in particular in Q_alpha when b is positive.

Source: MS93 (3.4), printed p.868. The actual replacement radical is arbitrary;
only the separate genuine component Sylow is transported. The central omega
attachment is included in the star bound.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)

def componentSylowActor (a : Vertex R) (P : Sylow 2 (Ltilde R a)) : Subgroup (FreeAmalgam R) :=
  (P : Subgroup (Ltilde R a)).map (Ltilde R a).subtype

def componentSylowSeed (a : Vertex R) (P : Sylow 2 (Ltilde R a)) : Subgroup (FreeAmalgam R) :=
  U R a ⊓ centralizer (componentSylowActor R a P : Set (FreeAmalgam R))

theorem exists_componentSylowSeed_act (a : Vertex R) (P : Sylow 2 (Ltilde R a))
    (g : FreeAmalgam R) :
    ∃ P' : Sylow 2 (Ltilde R (act R g a)),
      componentSylowSeed R (act R g a) P' =
        (componentSylowSeed R a P).map (MulAut.conj g⁻¹).toMonoidHom := by
  let e : Ltilde R a ≃* Ltilde R (act R g a) :=
    ((Ltilde R a).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).trans (MulEquiv.subgroupCongr (Ltilde_act R g a).symm)
  let := finite_stabilizer R a
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  let P' := P.mapSurjective (f := e.toMonoidHom) hsurj
  refine ⟨P',?_⟩
  have he : (Ltilde R (act R g a)).subtype.comp e.toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp (Ltilde R a).subtype := by ext x; rfl
  have hactor : componentSylowActor R (act R g a) P' =
      (componentSylowActor R a P).map (MulAut.conj g⁻¹).toMonoidHom := by
    change (((P.mapSurjective (f := e.toMonoidHom) hsurj : Sylow 2 (Ltilde R (act R g a))) :
      Subgroup (Ltilde R (act R g a))).map (Ltilde R (act R g a)).subtype)=_
    rw [Sylow.coe_mapSurjective,map_map,he,←map_map]
    rfl
  unfold componentSylowSeed
  rw [U_act,hactor,map_inf_centralizer_of_injective _ (MulAut.conj g⁻¹).injective]

omit [Finite M] in
theorem map_seed_normalized_at_act
    (Y : Subgroup (FreeAmalgam R)) {t : Vertex R}
    (hn : Q R t ≤ normalizer (Y : Set (FreeAmalgam R))) (g : FreeAmalgam R) :
    Q R (act R g t) ≤ normalizer
      (Y.map (MulAut.conj g⁻¹).toMonoidHom : Set (FreeAmalgam R)) := by
  rw [Q_act,←map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective]
  exact map_mono hn

theorem transported_seed_is_componentSylowSeed
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    (g : Mbar R) (h : Hbar R) :
    ∃ P' : Sylow 2 (Ltilde R (act R (g:FreeAmalgam R)⁻¹ (act R (h:FreeAmalgam R)⁻¹ (alpha R)))),
      ((Y.map (embedS R)).map (MulAut.conj (h:FreeAmalgam R)).toMonoidHom).map
        (MulAut.conj (g:FreeAmalgam R)).toMonoidHom =
        componentSylowSeed R _ P' ∧
      Q R (act R (g:FreeAmalgam R)⁻¹ (beta R)) ≤ normalizer
        (componentSylowSeed R _ P' : Set (FreeAmalgam R)) := by
  obtain ⟨P₁,hP₁⟩ := exists_componentSylowSeed_act R (alpha R) P (h:FreeAmalgam R)⁻¹
  obtain ⟨P₂,hP₂⟩ := exists_componentSylowSeed_act R _ P₁ (g:FreeAmalgam R)⁻¹
  simp only [inv_inv] at hP₁ hP₂
  have hseed : ((Y.map (embedS R)).map (MulAut.conj (h:FreeAmalgam R)).toMonoidHom).map
      (MulAut.conj (g:FreeAmalgam R)).toMonoidHom = componentSylowSeed R _ P₂ := by
    rw [hY,←hP₁,←hP₂]
  refine ⟨P₂,hseed,?_⟩
  have hh : (h:FreeAmalgam R) ∈ stabilizer R (beta R) := by
    simpa only [beta,stabilizer_h_base] using h.property
  have hhb : act R (h:FreeAmalgam R)⁻¹ (beta R)=beta R :=
    (stabilizer R (beta R)).inv_mem hh
  have h₁ := map_seed_normalized_at_act R _ hn (h:FreeAmalgam R)⁻¹
  simp only [hhb,inv_inv] at h₁
  have h₂ := map_seed_normalized_at_act R _ h₁ (g:FreeAmalgam R)⁻¹
  simpa only [inv_inv,hseed] using h₂

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

open Theory.GroupTheory CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open MSCentralOrbit
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_sourceStarAlpha_le_distant_core
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    {c : Vertex R} (hcc : color R c = false)
    (hac : (cosetGraph R).dist (alpha R) c + 2 ≤ geometry.b R) :
    sourceStarAlpha R Y ≤ Q R c := by
  have hbeta : (starSpan R Y).map (embedS R) =
      (⨆ h : Hbar R, (Y.map (embedS R)).map (MulAut.conj (h : FreeAmalgam R)).toMonoidHom) ⊔
        Z R (beta R) := by
    simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph R Y
  have hZaQ : Z R (alpha R) ≤ Q R c := Z_le_Q_of_dist_lt R (alpha R)
    (geometry.exists_critical (alpha R) rfl) (by
      rw [geometry.distance_constant (alpha R) rfl]
      change (cosetGraph R).dist (alpha R) c < geometry.b R
      omega)
  apply (sourceStarAlpha_le_iff R Y _).mpr
  intro g
  rw [hbeta,Subgroup.map_sup,Subgroup.map_iSup]
  apply sup_le
  · apply iSup_le
    intro h
    obtain ⟨P',hP',hn'⟩ := transported_seed_is_componentSylowSeed R Y P hY hn g h
    obtain ⟨hat,hdt⟩ := transported_seed_edges R g h
    rw [hP']
    exact original_two_edge_sylow_seed_le_distant_core R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq geometry hb
      (by simp only [action_preserves_color]; rfl) hcc hat hdt hac P' hn'
  · have hg : (g : FreeAmalgam R) ∈ stabilizer R (alpha R) := by
      simpa only [alpha,stabilizer_m_base] using g.property
    have hfix := mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R) hg)
    have hba : Z R (beta R) ≤ Z R (alpha R) := by
      change edgeOmega R (beta R) ≤ ⨆ b, ⨆ (_ : Adjacent R (alpha R) b), edgeOmega R b
      exact le_iSup_of_le (beta R) (le_iSup_of_le (base_adjacent R) le_rfl)
    exact ((map_mono hba).trans_eq hfix).trans hZaQ

theorem original_sourceStarAlpha_le_own_core
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    sourceStarAlpha R Y ≤ Q R (alpha R) := by
  have heven := geometry.even (alpha R) rfl
  rw [geometry.distance_constant (alpha R) rfl] at heven
  change Even (geometry.b R) at heven
  obtain ⟨n,hnn⟩ := heven
  exact original_sourceStarAlpha_le_distant_core R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq geometry hb Y P hY hn rfl (by simp only [SimpleGraph.dist_self]; omega)

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.SeedTransport
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowSeedCard
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.LargeDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.CriticalGeneration
/-!
# The actual bad star supplies a critical seed and order-four indices

A full component Sylow fixes at most sixteen elements on the original
moving cover over F4. Source2.1(vii) therefore chooses an escaping conjugate
of a bad transported star seed. The star radius puts that same seed in
Q_alpha and in the critical endpoint stabilizer, even when b=2. The adequate
large-displacement comparison then proves both critical indices are four.

The witness retains its literal two edges, genuine component Sylow, fixed
seed, edge normalizer, and membership in the original star. The replacement
radical is not assumed full Sylow, and no central complement is chosen.
Source: MS93 (2.1)(vii), (3.3)--(3.4), printed pp.856,867--868.
This is the actual first-star failure reduction, not the final contradiction.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource MSCentralOrbit SourceComparison
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]
theorem original_componentSylowSeed_card_le_sixteen
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
    {z : Vertex R} (hz : color R z = false) (P : Sylow 2 (Ltilde R z)) :
    Nat.card (componentSylowSeed R z P) ≤ 16 := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hconj,hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore
      hc hC hsq hz
  have hFc : Nat.card F.Carrier=4 := by rw [F.card_eq,hF]; norm_num
  let f₀ : Ltilde R z →* J := κ.comp (inclusion (Ltilde_le_stabilizer z))
  have hf₀ : f₀.range=(pResidual 2 H).map q := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hκL
  let f := e.groupEquiv.toMonoidHom.comp
    (f₀.codRestrict ((pResidual 2 H).map q) (fun x => hf₀ ▸ ⟨x,rfl⟩))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y,hy⟩ := (show (e.groupEquiv.symm x : J) ∈ f₀.range from hf₀.symm ▸ (e.groupEquiv.symm x).property)
    refine ⟨y,?_⟩
    change e.groupEquiv ⟨f₀ y,_⟩=x
    rw [show (⟨f₀ y,_⟩ : (pResidual 2 H).map q)=e.groupEquiv.symm x from Subtype.ext hy,
      e.groupEquiv.apply_symm_apply]
  have hfmark (x : Ltilde R z) : (e.groupEquiv.symm (f x) : J)=f₀ x := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨f₀ x,_⟩) : J)=f₀ x
    rw [e.groupEquiv.symm_apply_apply]
  have hfact (x : Ltilde R z) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (f x) v)) =
        (x : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam R)⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation (e.groupEquiv.symm (f x)) v))=_
    rw [hfmark]
    exact hconj (inclusion (Ltilde_le_stabilizer z) x) v
  let T := (P : Subgroup (Ltilde R z)).map (Ltilde R z).subtype
  let d : (P : Subgroup (Ltilde R z)) ≃* T :=
    (P : Subgroup (Ltilde R z)).equivMapOfInjective (Ltilde R z).subtype (Ltilde R z).subtype_injective
  let π : T →* L (K := F.Carrier) :=
    (f.comp (P : Subgroup (Ltilde R z)).subtype).comp d.symm.toMonoidHom
  let := finite_stabilizer R z
  let : Finite (Ltilde R z) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer z)) (inclusion_injective _)
  let S := P.mapSurjective (f := f) hf
  have hπ : π.range=(S : Subgroup (L (K := F.Carrier))) := by
    change π.range = (P.mapSurjective (f := f) hf : Subgroup _)
    rw [Sylow.coe_mapSurjective,MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective d.symm.toMonoidHom d.symm.surjective,
      ←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
  have hT (t : T) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (π t) v)) =
        (t : FreeAmalgam R)*j (Multiplicative.ofAdd v)*(t : FreeAmalgam R)⁻¹ := by
    have hh := hfact (d.symm t) v
    have hval : ((d.symm t : P) : FreeAmalgam R)=(t : FreeAmalgam R) :=
      congrArg Subtype.val (d.apply_symm_apply t)
    exact hval ▸ hh
  have hbound := centralizer_embedded_cover_sylow_card_le (U R z) T j hj hjr π S hπ
    (MovedSection.coverAction s e) hT (MovedSection.coverProjection s e) he
  rw [hFc] at hbound
  exact hbound

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}

theorem le_endpoint_stabilizer_of_radius_core_bound
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (K : Subgroup (FreeAmalgam R))
    (hK : ∀ c, color R c = false →
      (cosetGraph R).dist a c + 2 ≤ geometry.b R → K ≤ Q R c) :
    K ≤ stabilizer R e := by
  have heven : Even path.walk.length := by
    rw [path.shortest,path.critical.1]
    exact geometry.even a path.start_color
  have hlen := path.length_eq_b
  have htwo : 2 ≤ path.walk.length := by
    obtain ⟨n,hn⟩ := heven
    omega
  let c := path.walk.getVert (path.walk.length-2)
  let t := path.walk.getVert (path.walk.length-1)
  have hc : color R c=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at heven ⊢
    omega
  have hct : Adjacent R c t := by
    have hh := path.walk.adj_getVert_succ (i := path.walk.length-2) (by omega)
    have hi : path.walk.length-2+1=path.walk.length-1 := by omega
    rw [hi] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have hte : Adjacent R t e := by
    have hh := path.walk.adj_getVert_succ (i := path.walk.length-1) (by omega)
    have hi : path.walk.length-1+1=path.walk.length := by omega
    rw [hi,SimpleGraph.Walk.getVert_length] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have ht : color R t=true := by
    have hh := adjacent_color_ne R hct
    cases he : color R t <;> simp_all
  have hdist : (cosetGraph R).dist a c + 2 ≤ geometry.b R := by
    rw [show (cosetGraph R).dist a c=path.walk.length-2 from path.dist_start (Nat.sub_le _ _)]
    omega
  exact ((hK c hc hdist).trans (Q_le_adjacent_h R ht hct)).trans
    (fun _ hx => hx.2 e hte)

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

open Theory.GroupTheory CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open MSCentralOrbit
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_sourceStarAlpha_le_critical_endpoint_stabilizer
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc' : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    sourceStarAlpha R Y ≤ stabilizer R z := by
  apply le_endpoint_stabilizer_of_radius_core_bound path hb
  intro c hc hac
  exact original_sourceStarAlpha_le_distant_core R hms hp hne hQR hself hfaith
    q hq hcore hc' hC hsq geometry hb Y P hY hn hc hac

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

open Theory.GroupTheory CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open MSCentralOrbit
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

theorem original_bad_star_critical_seed
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hgen : pResidual 2 H ⊔ R = ⊤)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    (hbad : ¬ ⁅sourceStarAlpha R Y,Ltilde R (alpha R)⁆ ≤ Z R (alpha R)) :
    ∃ d t : Vertex R, ∃ P' : Sylow 2 (Ltilde R d),
      color R d=false ∧ Adjacent R (alpha R) t ∧ Adjacent R d t ∧
      Q R t ≤ normalizer (componentSylowSeed R d P' : Set (FreeAmalgam R)) ∧
      componentSylowSeed R d P' ≤ sourceStarAlpha R Y ∧
      ¬ Z R z ≤ normalizer ((componentSylowSeed R d P' ⊔ Z R (alpha R) :
        Subgroup (FreeAmalgam R)) : Set _) := by
  obtain ⟨g,h,hbadSeed⟩ := exists_bad_transported_seed R Y hbad
  let A := ((Y.map (embedS R)).map (MulAut.conj (h : FreeAmalgam R)).toMonoidHom).map
    (MulAut.conj (g : FreeAmalgam R)).toMonoidHom
  let d := act R (g : FreeAmalgam R)⁻¹ (act R (h : FreeAmalgam R)⁻¹ (alpha R))
  let t := act R (g : FreeAmalgam R)⁻¹ (beta R)
  obtain ⟨P',hP',hn'⟩ := transported_seed_is_componentSylowSeed R Y P hY hn g h
  have hA : A=componentSylowSeed R d P' := hP'
  have hd : color R d=false := by simp only [d,action_preserves_color]; rfl
  have hAU : A ≤ U R d := hA.le.trans inf_le_left
  have hAn : Q R t ≤ normalizer (A : Set (FreeAmalgam R)) := by rw [hA]; exact hn'
  have hcard : Nat.card A ≤ 64 := by
    rw [hA]
    exact (original_componentSylowSeed_card_le_sixteen R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq hd P').trans (by decide)
  have hAstar : A ≤ sourceStarAlpha R Y := by
    have hbeta : (starSpan R Y).map (embedS R) =
        (⨆ h : Hbar R, (Y.map (embedS R)).map (MulAut.conj (h : FreeAmalgam R)).toMonoidHom) ⊔
          Z R (beta R) := by
      simpa only [map_map,embedM_comp_subtype] using starSpan_map_graph R Y
    have hYbeta : (Y.map (embedS R)).map (MulAut.conj (h : FreeAmalgam R)).toMonoidHom ≤
        (starSpan R Y).map (embedS R) := by
      rw [hbeta]
      exact (le_iSup (fun k : Hbar R => (Y.map (embedS R)).map
        (MulAut.conj (k : FreeAmalgam R)).toMonoidHom) h).trans le_sup_left
    exact (map_mono hYbeta).trans ((sourceStarAlpha_le_iff R Y _).mp le_rfl g)
  obtain ⟨hat,hdt⟩ := transported_seed_edges R g h
  obtain ⟨k,hk,hnk⟩ := exists_critical_escape_of_bad_small_seed R hp hQR hgen
    q hq hcore hC (by rw [hc]; norm_num) geometry hb
    (MSCentralOrbit.edgeCentralizerCondition R hp hQR hfaith) rfl hd hat hdt
    path.critical A hAU hcard hbadSeed hAn
  let A' := A.map (MulAut.conj k⁻¹).toMonoidHom
  have hkstar : (sourceStarAlpha R Y).map (MulAut.conj k⁻¹).toMonoidHom =
      sourceStarAlpha R Y := mem_normalizer_iff_map_conj_eq.mp
        (sourceStarAlpha_normalized R Y ((stabilizer R (alpha R)).inv_mem hk))
  have hkZ : (Z R (alpha R)).map (MulAut.conj k⁻¹).toMonoidHom = Z R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R)
      ((stabilizer R (alpha R)).inv_mem hk))
  have hA'star : A' ≤ sourceStarAlpha R Y := (map_mono hAstar).trans_eq hkstar
  have hnjoin : ¬ Z R z ≤ normalizer ((A' ⊔ Z R (alpha R) : Subgroup (FreeAmalgam R)) : Set _) := by
    simpa only [Subgroup.map_sup,hkZ] using hnk
  obtain ⟨P'',hP''⟩ := exists_componentSylowSeed_act R d P' k
  have hAA : A'=componentSylowSeed R (act R k d) P'' := by
    change A.map (MulAut.conj k⁻¹).toMonoidHom = _
    rw [hA]
    exact hP''.symm
  have hka : act R k (alpha R)=alpha R := hk
  have hat' : Adjacent R (alpha R) (act R k t) := by
    simpa only [hka] using (adjacent_act_iff R k (alpha R) t).mpr hat
  have hdt' : Adjacent R (act R k d) (act R k t) :=
    (adjacent_act_iff R k d t).mpr hdt
  have hn' := map_seed_normalized_at_act R A hAn k
  change Q R (act R k t) ≤ normalizer (A' : Set (FreeAmalgam R)) at hn'
  rw [hAA] at hn'
  refine ⟨act R k d,act R k t,P'',(action_preserves_color R k d).trans hd,
    hat',hdt',hn',?_,?_⟩
  · exact hAA ▸ hA'star
  · exact hAA ▸ hnjoin

theorem original_bad_star_critical_indices_eq_four
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hgen : pResidual 2 H ⊔ R = ⊤)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    {z : Vertex R} (path : CriticalPath R geometry (alpha R) z)
    (Y : Subgroup R) (P : Sylow 2 (Ltilde R (alpha R)))
    (hY : Y.map (embedS R)=componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)))
    (hbad : ¬ ⁅sourceStarAlpha R Y,Ltilde R (alpha R)⁆ ≤ Z R (alpha R)) :
    (Q R z).relIndex (Z R (alpha R))=4 ∧ (Q R (alpha R)).relIndex (Z R z)=4 := by
  obtain ⟨d,t,P',hd,hat,hdt,hn',hseed,hnot⟩ := original_bad_star_critical_seed R hms hp hne hQR
    hgen hself hfaith q hq hcore hc hC hsq geometry hb path Y P hY hn hbad
  exact original_critical_indices_eq_four_of_core_seed R hms hp hne hQR hself hfaith
    q hq hcore hc hC hsq path hb (componentSylowSeed R d P')
    (hseed.trans (original_sourceStarAlpha_le_critical_endpoint_stabilizer R hms hp hne hQR
      hself hfaith q hq hcore hc hC hsq geometry hb path Y P hY hn))
    (hseed.trans (original_sourceStarAlpha_le_own_core R hms hp hne hQR hself hfaith
      q hq hcore hc hC hsq geometry hb Y P hY hn)) hnot

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four

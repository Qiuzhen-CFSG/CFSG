module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.NinePathCentralizer

/-!
# The escaping centralizer branch of DGS (12.7)

On x--m--y--z--w--c, let y be the marked Suzuki vertex and
A = C_(V_x)(t). If A escapes Q_y, its image has a nonidentity element
in the Sylow coming from m. The remote span V_w maps onto the full
omega of the distinct Sylow coming from z; its order is derived from
the critical pair (c,y). Suzuki omega generation then proves
(A join V_w) join Q_y = star_y. The core fixes the neighborhood, so
A join V_w itself is transitive there. If t centralizes V_w and lies
in Q_m and Q_y, this propagates to centralization of the whole V_y.

Both orientations, the actual original quotient marking, and the
completion inclusion are retained. The common Sylows, critical pair,
and linear marking are earlier source inputs. The nine-path application
in NinePathUntrappedCentralizer discharges the remote-span centralization
premise using the original path fixer. This module does not assert the
subsequent linear-neighborhood transitivity contradiction, the binary
case, Suzuki selection, or the full (12.8)--(12.9)/(13.1) assembly.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7), printed p.184, the branch A not contained in Q_beta, using
(12.3)(a), (12.5) and the full-omega generation theorem for q > 2.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- An escaping subgroup in one incoming core and the remote span through
another incoming edge generate the actual Suzuki star modulo its core. -/
theorem source_suzuki_span_escape_generation
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {c w z : Vertex (reducedFamily L S)}
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) (!i))
    (hc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) i))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (D : Subgroup (G₀ L S))
    (hDm : D ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hesc : ¬ D ≤ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    (D ⊔ V F w 1) ⊔ Q F (base F i) = star L S i ∧
      (D.map (G₀ L S).subtype ⊔ (V F w 1).map (G₀ L S).subtype) ⊔
        (Q F (base F i)).map (G₀ L S).subtype = starredParabolic L S (if i then 1 else 0) := by
  let F := reducedFamily L S
  let P := star L S i
  let y := base F i
  let m := base F (!i)
  let W := V F w 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite P := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans eSuz).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans eSuz).surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 P := by
    ext t
    change eSuz ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 P) t)) = 1 ↔ t ∈ pCore 2 P
    rw [map_eq_one_iff _ eSuz.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff t
  have hkQ : f.ker = (Q F y).subgroupOf P := by
    rw [hk,←star_core h i]
    exact (comap_map_eq_self_of_injective P.subtype_injective _).symm
  have hmP : Q F m ≤ P := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hzP : Q F z ≤ P := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hyP : Q F y ≤ P := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have hDP := hDm.trans hmP
  have hWz : W ≤ Q F z := V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hwz
  have hWP := hWz.trans hzP
  obtain ⟨U,hU,_,_⟩ := source_common_sylow_core_index h i eSuz T hT
  obtain ⟨J,hJ,_,_⟩ := source_common_sylow_core_index h i eSuz R hR
  let E := (W.subgroupOf P).map f
  let := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb w
  let : IsElementaryAbelian 2 (W.subgroupOf P) := IsElementaryAbelian.subgroupOf hWP
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
  have hEJ : E ≤ (J : Subgroup (SuzukiMatrixGroup n)) := hJ ▸ map_mono (subgroupOf_mono P hWz)
  have hEO : E ≤ omegaOneAmbient (J : Subgroup (SuzukiMatrixGroup n)) := by
    rw [←omegaOneAmbient_eq_self E]
    exact omegaOneAmbient_mono hEJ
  have hi : (Q F y).relIndex W = 2^(2*n+1) := by
    simpa only [inf_relIndex_left] using
      (source_suzuki_first_index h i hb hc hwc hwz hyz hn eSuz eLin R hR).1
  have hEcard : Nat.card E = 2^(2*n+1) := by
    rw [←relIndex_ker,hkQ,relIndex_subgroupOf hWP]
    exact hi
  have hE : E = omegaOneAmbient (J : Subgroup (SuzukiMatrixGroup n)) :=
    eq_of_le_of_card_ge hEO (by rw [suzukiSylow_omega_card hn (MulEquiv.refl _) J,hEcard])
  have hgen := star_three_core_generation h i hyz hzn T R hT hR
  have hUJ : (U : Subgroup (SuzukiMatrixGroup n)) ⊔ J = ⊤ := by
    have he : (Q F m).subgroupOf P ⊔ (Q F z).subgroupOf P ⊔ (Q F y).subgroupOf P = ⊤ := by
      apply map_injective P.subtype_injective
      rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hmP,
        map_subgroupOf_eq_of_le hzP,map_subgroupOf_eq_of_le hyP,
        ←MonoidHom.range_eq_map,range_subtype]
      exact hgen.symm
    have hh := congrArg (Subgroup.map f) he
    rw [Subgroup.map_sup,Subgroup.map_sup,hU,hJ,←hkQ,Subgroup.map_ker_self,sup_bot_eq,
      Subgroup.map_top_of_surjective _ hf] at hh
    exact hh
  have hneUJ : U ≠ J := by
    intro he
    rw [he,sup_idem] at hUJ
    exact (suzuki_rankOneSylowFacts n J).proper.not_ge (hUJ ▸ J.toSubgroup.le_normalizer)
  obtain ⟨t,ht,htQ⟩ := Set.not_subset.mp hesc
  let u : P := ⟨t,hDP ht⟩
  have hfu : f u ≠ 1 := by
    intro he
    have hh : u ∈ f.ker := he
    rw [hkQ] at hh
    exact htQ hh
  have hfuU : f u ∈ (U : Subgroup (SuzukiMatrixGroup n)) := by
    rw [←hU]
    exact mem_map_of_mem f (hDm ht)
  have hfuN : f u ∉ normalizer (J : Set (SuzukiMatrixGroup n)) := by
    intro hh
    have hboth : f u ∈ (U : Subgroup (SuzukiMatrixGroup n)) ⊓ normalizer (J : Set _) := ⟨hfuU,hh⟩
    rw [U.isPGroup'.inf_normalizer_sylow J] at hboth
    exact hneUJ (suzuki_sylow_eq_of_inf_ne_bot_all n U J (by
      intro he
      rw [he,mem_bot] at hboth
      exact hfu hboth))
  have htop : ((D.subgroupOf P) ⊔ W.subgroupOf P).map f = ⊤ := by
    rw [Subgroup.map_sup]
    apply top_unique
    rw [←suzukiSylow_omega_sup_zpowers_eq_top hn J (f u) hfuN,←hE]
    exact sup_le le_sup_right ((zpowers_le.mpr (mem_map_of_mem f ht)).trans le_sup_left)
  have he := congrArg (Subgroup.comap f) htop
  rw [comap_map_eq,comap_top,hk] at he
  have hh := congrArg (Subgroup.map P.subtype) he
  rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hDP,map_subgroupOf_eq_of_le hWP,
    ←MonoidHom.range_eq_map,range_subtype] at hh
  change (D ⊔ W) ⊔ P.pCoreIn 2 = P at hh
  rw [star_core h i] at hh
  refine ⟨hh,?_⟩
  have ho := congrArg (Subgroup.map (G₀ L S).subtype) hh
  rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le (star_le_completion _)] at ho
  exact ho


private theorem star_supplement_transitive
    (h : HypothesisF11 L S) (i : Bool) (E : Subgroup (G₀ L S))
    (hgen : E ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i) = star L S i)
    {v : Vertex (reducedFamily L S)}
    (hv : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) v) :
    ∃ g ∈ E, g • base (reducedFamily L S) (!i) = v := by
  let F := reducedFamily L S
  let P := star L S i
  let y := base F i
  let m := base F (!i)
  have hEP : E ≤ P := le_sup_left.trans hgen.le
  have hQP : Q F y ≤ P := le_sup_right.trans hgen.le
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨g,hg,hgv⟩ := star_locally_transitive h i hadj hv
  have hs : E.subgroupOf P ⊔ (Q F y).subgroupOf P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hEP,map_subgroupOf_eq_of_le hQP,
      ←MonoidHom.range_eq_map,range_subtype]
    exact hgen
  let : ((Q F y).subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    ((star_le_stabilizer i).trans (stabilizer_normalizes_Q F y))
  obtain ⟨u,hu,q,hq,he⟩ := mem_sup_of_normal_right.mp
    (show (⟨g,hg⟩ : P) ∈ E.subgroupOf P ⊔ (Q F y).subgroupOf P from hs ▸ mem_top _)
  have hqm : (q : G₀ L S) • m = m := (source_Z_Q_U (reduced_triple h) y).2 hq m
    ((mem_ball_one F y m).mpr (.inl hadj))
  refine ⟨u,hu,?_⟩
  have he' := congrArg Subtype.val he
  change (u : G₀ L S) * (q : G₀ L S) = g at he'
  rw [←he',mul_smul,hqm] at hgv
  exact hgv

/-- In the untrapped branch the generated centralizer is transitive on the
middle neighborhood and centralizes its entire span, with original maps. -/
theorem source_suzuki_untrapped_centralizer_propagation
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {x c w z : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hzn : z ≠ base (reducedFamily L S) (!i))
    (hc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) i))
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (t : G₀ L S)
    (htm : t ∈ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hty : t ∈ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hW : V (reducedFamily L S) w 1 ≤ centralizer ({t} : Set (G₀ L S)))
    (hesc : ¬ V (reducedFamily L S) x 1 ⊓ centralizer ({t} : Set (G₀ L S)) ≤
      Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let E := (V F x 1 ⊓ centralizer ({t} : Set (G₀ L S))) ⊔ V F w 1
    (∀ v, (graph F).Adj (base F i) v → ∃ g ∈ E, g • base F (!i) = v) ∧
      V F (base F i) 1 ≤ centralizer ({t} : Set (G₀ L S)) ∧
      (V F (base F i) 1).map (G₀ L S).subtype ≤ centralizer ({(t : G)} : Set G) := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let A := V F x 1 ⊓ centralizer ({t} : Set (G₀ L S))
  let E := A ⊔ V F w 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hAm : A ≤ Q F m := inf_le_left.trans (V_le_neighbor_Q F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb hxm)
  have hgen : E ⊔ Q F y = star L S i :=
    (source_suzuki_span_escape_generation h i hb hyz hwz hwc hzn hc hn eSuz eLin T R hT hR A hAm hesc).1
  have htrans := fun v hv => star_supplement_transitive h i E hgen (v := v) hv
  have hEC : E ≤ centralizer ({t} : Set (G₀ L S)) := sup_le inf_le_right hW
  have hZC (v : Vertex F) (htv : t ∈ Q F v) : Z F v ≤ centralizer ({t} : Set (G₀ L S)) := by
    intro u hu a ha
    have he : a = t := Set.mem_singleton_iff.mp ha
    subst a
    exact Z_centralizes_Q F v (source_Z_Q_U (reduced_triple h) v).1 hu t htv
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hV : V F y 1 ≤ centralizer ({t} : Set (G₀ L S)) := by
    rw [V_eq_center_sup_neighbor_conjugates F E
      ((le_sup_left.trans hgen.le).trans (star_le_stabilizer i)) hadj htrans]
    exact sup_le (hZC y hty) (conjugateSpanBy_le (hZC m htm)
      (hEC.trans (centralizer ({t} : Set (G₀ L S))).le_normalizer))
  refine ⟨htrans,hV,?_⟩
  rintro u ⟨v,hv,rfl⟩ a ha
  have he : a = (t : G) := Set.mem_singleton_iff.mp ha
  subst a
  exact congrArg (fun q : G₀ L S => (q : G)) (hV hv t (Set.mem_singleton t))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

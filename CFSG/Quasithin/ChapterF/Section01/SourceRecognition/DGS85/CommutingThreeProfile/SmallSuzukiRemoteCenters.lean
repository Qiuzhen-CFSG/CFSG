module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.RemoteCenterPropagation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiNeighborOrbits
public import Theory.GroupAction.PrimeDegreeCoprimeIndex
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.NonlinearCoreGeneration

/-!
# Remote critical centers at the small Suzuki endpoint

On the literal six-edge segment a-x-m-y-z-w-c, criticality makes the
images of Z_a and Z_c nontrivial in the distinct quotient Sylows attached
to m and z. Their join cannot be a two-group. Its index in the order-twenty
quotient is therefore coprime to five, so it acts transitively on the
actual five-point neighborhood. This uses no full-Suzuki generation by
two involutions, which would be false at parameter zero.

The same actual center join propagates centralization of a subgroup in
the four indicated full cores to the whole middle span. The original
completion inclusion is retained. This is the small-parameter replacement
of the first propagation step of DGS (12.7), printed p.184.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped Pointwise
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Two actual remote critical centers are transitive at the original Sz(2)
vertex. No numerical center-image premise is needed. -/
theorem small_suzuki_remote_critical_center_transitive
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    {a x z w c : Vertex (reducedFamily L S)}
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hne : z ≠ base (reducedFamily L S) (!i))
    (hca : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hcc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    : ∀ v, (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) v →
      ∃ g ∈ Z (reducedFamily L S) a ⊔ Z (reducedFamily L S) c,
        g • base (reducedFamily L S) (!i) = v := by
  let F := reducedFamily L S
  let A := star L S i
  let y := base F i
  let m := base F (!i)
  let E := Z F a ⊔ Z F c
  let H := E ⊔ Q F y
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective
    (inclusion (star_le_stabilizer (L := L) (S := S) i)) (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans e).surjective.comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext t
    change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff t
  have hkQ : f.ker = (Q F y).subgroupOf A := by
    rw [hk,←star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have haQ : Z F a ≤ Q F m := CommutingNontrivial.Z_le_Q_of_dist_lt_b F hZ a m
    (lt_of_le_of_lt ((graph F).dist_le (Walk.cons hxa.symm (Walk.cons hxm .nil))) hb)
    (reduced_kernel_sylow h m)
  have hcQ : Z F c ≤ Q F z := CommutingNontrivial.Z_le_Q_of_dist_lt_b F hZ c z
    (lt_of_le_of_lt ((graph F).dist_le (Walk.cons hwc.symm (Walk.cons hwz .nil))) hb)
    (reduced_kernel_sylow h z)
  have hmA : Q F m ≤ A := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hzA : Q F z ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hyA : Q F y ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have haA : Z F a ≤ A := haQ.trans hmA
  have hcA : Z F c ≤ A := hcQ.trans hzA
  have hEA : E ≤ A := sup_le haA hcA
  have hHA : H ≤ A := sup_le hEA hyA
  obtain ⟨P,hP,_,_⟩ := source_common_sylow_core_index h i e T hT
  obtain ⟨U,hU,_,_⟩ := source_common_sylow_core_index h i e R hR
  have hgen := star_three_core_generation h i hyz hne T R hT hR
  have hPU : (P : Subgroup (SuzukiMatrixGroup 0)) ⊔ U = ⊤ := by
    have he : (Q F m).subgroupOf A ⊔ (Q F z).subgroupOf A ⊔ (Q F y).subgroupOf A = ⊤ := by
      apply map_injective A.subtype_injective
      rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hmA,
        map_subgroupOf_eq_of_le hzA,map_subgroupOf_eq_of_le hyA,
        ←MonoidHom.range_eq_map,range_subtype]
      exact hgen.symm
    have hh := congrArg (Subgroup.map f) he
    rw [Subgroup.map_sup,Subgroup.map_sup,hP,hU,←hkQ,Subgroup.map_ker_self,
      sup_bot_eq,Subgroup.map_top_of_surjective _ hf] at hh
    exact hh
  have hnePU : P ≠ U := by
    intro he
    rw [he,sup_idem] at hPU
    exact (suzuki_rankOneSylowFacts 0 U).proper.not_ge (hPU ▸ U.toSubgroup.le_normalizer)
  have himage_ne (v : Vertex F) (hvA : Z F v ≤ A) (hv : IsCriticalPair F v y) :
      ((Z F v).subgroupOf A).map f ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff ((Z F v).subgroupOf A)).mp he
    rw [hkQ] at hh
    apply hv.2
    intro t ht
    exact (source_Z_Q_U (reduced_triple h) y).2
      (hh (show (⟨t,hvA ht⟩ : A) ∈ (Z F v).subgroupOf A from ht))
  let K := H.subgroupOf A
  have hkerK : f.ker ≤ K := by
    rw [hkQ]
    exact fun _ ht => mem_sup_right ht
  have hnot : ¬ IsPGroup 2 (K.map f) := by
    intro hp
    obtain ⟨J,hJ⟩ := hp.exists_le_sylow
    have haP : ((Z F a).subgroupOf A).map f ≤ P := hP ▸ map_mono (subgroupOf_mono A haQ)
    have hcU : ((Z F c).subgroupOf A).map f ≤ U := hU ▸ map_mono (subgroupOf_mono A hcQ)
    have haJ : ((Z F a).subgroupOf A).map f ≤ J :=
      (map_mono (subgroupOf_mono A (show Z F a ≤ H from le_sup_left.trans le_sup_left))).trans hJ
    have hcJ : ((Z F c).subgroupOf A).map f ≤ J :=
      (map_mono (subgroupOf_mono A (show Z F c ≤ H from le_sup_right.trans le_sup_left))).trans hJ
    have hPJ : P = J := smallSuzuki_sylow_eq_of_inf_ne_bot P J (by
      intro he
      exact himage_ne a haA hca (bot_unique ((le_inf haP haJ).trans_eq he)))
    have hUJ : U = J := smallSuzuki_sylow_eq_of_inf_ne_bot U J (by
      intro he
      exact himage_ne c hcA hcc (bot_unique ((le_inf hcU hcJ).trans_eq he)))
    exact hnePU (hPJ.trans hUJ.symm)
  have hcop : Nat.Coprime 5 K.index := by
    rw [←K.index_map_eq hf hkerK]
    apply Nat.prime_five.coprime_iff_not_dvd.mpr
    rintro ⟨n,hn⟩
    have hh := (K.map f).card_mul_index
    rw [suzukiZero_card,hn] at hh
    have hd : Nat.card (K.map f) ∣ 2^2 := ⟨n,by nlinarith⟩
    exact hnot (IsPGroup.of_card_dvd_pow hd)
  let P₀ : Sylow 2 (SuzukiMatrixGroup 0) := T.mapSurjective (f := f) hf
  have hPT : (P₀ : Subgroup (SuzukiMatrixGroup 0)).comap f = (T : Subgroup A) := by
    apply comap_map_eq_self
    rw [hk]
    exact pCore_isPGroup.le_sylow_of_normal T
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  obtain ⟨T₀,hT₀⟩ := base_star_sylow_normalizer h i
  have hTfix : (T : Subgroup A).map A.subtype ≤ stabilizer F m := by
    rw [hT]
    exact sup_le (Q_le_stabilizer F _) (((source_Z_Q_U (reduced_triple h) y).2.trans
      (ballKernel_one_le_edge F hadj)).trans inf_le_right)
  have heT : T = T₀ := sylow_le_normalizer_eq T₀ T (by
    rw [←hT₀]
    exact fun t ht => hTfix (mem_map_of_mem A.subtype ht))
  obtain ⟨p,hp,_⟩ := CommutingOneProfile.small_suzuki_orbits P₀
  have hstab : (MulAction.stabilizer (SuzukiMatrixGroup 0) p).comap f =
      MulAction.stabilizer A m := by
    rw [←hp]
    change (normalizer ((P₀ : Subgroup (SuzukiMatrixGroup 0)) : Set (SuzukiMatrixGroup 0))).comap f = _
    rw [comap_normalizer_eq_of_surjective _ hf,hPT,Sylow.coe_coe,heT,←hT₀]
    rfl
  have hidx : (MulAction.stabilizer A m).index = 5 := by
    rw [←hstab,index_comap_of_surjective _ hf,MulAction.index_stabilizer_of_transitive,
      suzukiOvoid_card]
    norm_num
  let X := MulAction.orbit A m
  have hcard : Nat.card X = 5 := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer A m),←index_eq_card,hidx]
  let : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : MulAction.IsPretransitive K X :=
    MulAction.isPretransitive_of_prime_card_of_coprime_index (by decide) hcard K hcop
  have hnE : E ≤ normalizer (Q F y : Set (G₀ L S)) :=
    (hEA.trans (star_le_stabilizer i)).trans (stabilizer_normalizes_Q F y)
  intro v hv
  obtain ⟨t,ht,htm⟩ := star_locally_transitive h i hadj hv
  let xm : X := ⟨m,MulAction.mem_orbit_self m⟩
  let xv : X := ⟨v,⟨(⟨t,ht⟩ : A),htm⟩⟩
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq K xm xv
  have hum : ((u : A) : G₀ L S) • m = v := congrArg Subtype.val hu
  have huH : ((u : A) : G₀ L S) ∈ H := u.property
  have hu' : ((u : A) : G₀ L S) ∈ (E : Set (G₀ L S)) * (Q F y : Set (G₀ L S)) := by
    rw [←coe_mul_of_left_le_normalizer_right E (Q F y) hnE]
    exact huH
  obtain ⟨g,hg,q,hq,he⟩ := hu'
  have hqm : q • m = m := ((source_Z_Q_U (reduced_triple h) y).2.trans
    ((ballKernel_one_le_edge F hadj).trans inf_le_right)) hq
  refine ⟨g,hg,?_⟩
  change g*q = ((u : A) : G₀ L S) at he
  rw [←he,mul_smul,hqm] at hum
  exact hum

/-- The same remote-center action centralizes the full middle span for a
subgroup in the four actual cores, also after the original inclusion. -/
theorem small_suzuki_remote_critical_center_propagation
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    {a x z w c : Vertex (reducedFamily L S)}
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (hyz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hwz : (graph (reducedFamily L S)).Adj w z)
    (hwc : (graph (reducedFamily L S)).Adj w c)
    (hne : z ≠ base (reducedFamily L S) (!i))
    (hca : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hcc : IsCriticalPair (reducedFamily L S) c (base (reducedFamily L S) i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (D : Subgroup (G₀ L S))
    (hDa : D ≤ Q (reducedFamily L S) a) (hDc : D ≤ Q (reducedFamily L S) c)
    (hDm : D ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hDy : D ≤ Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    V (reducedFamily L S) (base (reducedFamily L S) i) 1 ≤ centralizer (D : Set (G₀ L S)) ∧
      (V (reducedFamily L S) (base (reducedFamily L S) i) 1).map (G₀ L S).subtype ≤
        centralizer (D.map (G₀ L S).subtype : Set G) := by
  let F := reducedFamily L S
  let y := base F i
  let m := base F (!i)
  let E := Z F a ⊔ Z F c
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have htrans := small_suzuki_remote_critical_center_transitive h i hb e
    hxa hxm hyz hwz hwc hne hca hcc T R hT hR
  have hZQ (v u : Vertex F) (hvu : (graph F).dist v u ≤ 2) : Z F v ≤ Q F u :=
    CommutingNontrivial.Z_le_Q_of_dist_lt_b F (fun v => (source_Z_Q_U (reduced_triple h) v).1)
      v u (lt_of_le_of_lt hvu hb) (reduced_kernel_sylow h u)
  have hEA : E ≤ star L S i := sup_le
    ((hZQ a m ((graph F).dist_le (Walk.cons hxa.symm (Walk.cons hxm .nil)))).trans
      ((le_sup_left.trans hT.ge).trans (map_subtype_le _)))
    ((hZQ c z ((graph F).dist_le (Walk.cons hwc.symm (Walk.cons hwz .nil)))).trans
      ((le_sup_left.trans hR.ge).trans (map_subtype_le _)))
  have hZC (v : Vertex F) (hv : D ≤ Q F v) :
      Z F v ≤ centralizer (D : Set (G₀ L S)) :=
    (Z_centralizes_Q F v (source_Z_Q_U (reduced_triple h) v).1).trans (centralizer_le hv)
  have hEC : E ≤ centralizer (D : Set (G₀ L S)) := sup_le (hZC a hDa) (hZC c hDc)
  have hadj : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hV : V F y 1 ≤ centralizer (D : Set (G₀ L S)) := by
    rw [V_eq_center_sup_neighbor_conjugates F E (hEA.trans (star_le_stabilizer i)) hadj htrans]
    exact sup_le (hZC y hDy) (conjugateSpanBy_le (hZC m hDm)
      (hEC.trans (centralizer (D : Set (G₀ L S))).le_normalizer))
  refine ⟨hV,?_⟩
  rw [←inf_eq_left] at hV ⊢
  rw [map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,hV]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer

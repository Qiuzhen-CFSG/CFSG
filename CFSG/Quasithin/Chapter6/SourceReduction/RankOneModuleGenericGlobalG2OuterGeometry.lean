module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2OuterRootAction
public import Theory.GroupTheory.PGroup.NormalSubgroups
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2ShortSylow
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2RootPair

/-!
# The original outer involution's centralizer normalizer

Write E = C_T(t) for an involution normalizing the marked Hall torus. Every
involutory additive root action has a nonzero fixed vector. The actual root
product law shows that centralizing these fixed roots inside S forces an
element into the highest root, and that the fixed B–E pair does not commute.
The literal quotient field action has abelian image and kernel S, so E′ lies
in S. The p-group center theorem now makes Z(E) intersect E′ nontrivial;
transport through the same parabolic map places it in Z(O²(H)).

This intersection is characteristic in E. The already established TI
property of the right center therefore gives N_G(E) <= N_G(O²(H)). Applying
the normalizer condition in an actual ambient-centralizer Sylow subgroup,
whose order is at least q⁴, produces a strict two-group enlargement of E
inside N_G(O²(H)) intersect C_G(t), since |E| < q⁴.

This proves the normalizer-control step of F.4.37 in the G₂ row, including
field four, and supplies its actual outer-involution consumer. Excluding the
local enlargement still requires the local centralizer Sylow calculation;
no ambient Sylow placement or S=T is assumed here. Original uniqueness,
exhaustive comparison and completion recognition retain their existing
assembly obligations. The Chapter 12 companion keeps the original torus and
quotient field markings.

Source: Aschbacher–Smith F.4.37–38, printed pp.293–294, and 5.3.3, p.659
(`refs/quasithin.pdf`). The root formulas retain the ATLAS attribution in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. The internal imports reuse
this source family's inverse Sylow map and highest-root center calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2OuterGeometry
variable {F : Type*} [Field F] [CharP F 2]

private theorem nonzero_fixed (ρ : F ≃+ F) (hρ : Function.Involutive ρ) :
    ∃ x : F, x ≠ 0 ∧ ρ x=x := by
  by_cases h : ρ 1=1
  · exact ⟨1,one_ne_zero,h⟩
  · refine ⟨1+ρ 1,?_,?_⟩
    · intro hh
      have he : ρ 1=1 := by
        calc
          ρ 1 = 1+(1+ρ 1) := by rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add]
          _ = 1 := by rw [hh,add_zero]
      exact h he
    · rw [map_add,hρ]
      exact add_comm _ _

private theorem central_parameters (v w : Fin 6 → F) (hw : ∀ i, w i ≠ 0)
    (hc : ∀ j : Fin 6, j ≠ 5 →
      unipotentProductParameters (Pi.single j (w j)) v =
      unipotentProductParameters v (Pi.single j (w j))) :
    v = ![v 0,0,0,0,0,0] := by
  have htwo : (2:F)=0 := CharP.cast_eq_zero F 2
  have hthree : (3:F)=1 := by linear_combination htwo
  have h5 : v 5=0 := by
    have hh := congrFun (hc 4 (by decide)) 3
    simp [unipotentProductParameters] at hh
    exact hh.resolve_left (hw 4)
  have h4 : v 4=0 := by
    have hh := congrFun (hc 1 (by decide)) 0
    simp [unipotentProductParameters,h5] at hh
    exact hh.resolve_left (hw 1)
  have h3 : v 3=0 := by
    have hh := congrFun (hc 2 (by decide)) 0
    simp [unipotentProductParameters,h5,hthree] at hh
    exact hh.resolve_left (hw 2)
  have h2 : v 2=0 := by
    have hh := congrFun (hc 3 (by decide)) 0
    simp [unipotentProductParameters,h5,hthree] at hh
    exact hh.resolve_right (hw 3)
  have h1 : v 1=0 := by
    have hh := congrFun (hc 4 (by decide)) 0
    simp [unipotentProductParameters,h5] at hh
    exact hh.resolve_right (hw 4)
  ext i
  fin_cases i <;> simp [h1,h2,h3,h4,h5]

/-- Fixed points on each root already force their unipotent centralizer into
 the highest root, including when the fixed field has order two. -/
private theorem centralizer_fixed_roots (ρ : Fin 6 → F ≃+ F)
    (hρ : ∀ i, Function.Involutive (ρ i)) (x : Model F) (hx : x∈unipotent)
    (hc : ∀ (i : Fin 6) (u : F), ρ i u=u →
      Commute x (unipotentProduct (Pi.single i u))) : x∈highestRoot := by
  choose w hw hwfix using fun i => nonzero_fixed (ρ i) (hρ i)
  rw [unipotent_eq_range] at hx
  obtain ⟨v,rfl⟩ := hx
  have hv := central_parameters v w hw (fun j _ => by
    apply unipotentProduct_injective
    rw [←unipotentProduct_mul,←unipotentProduct_mul]
    exact (hc j (w j) (hwfix j)).eq.symm)
  refine ⟨Multiplicative.ofAdd (v 0),?_⟩
  change rootA (v 0)=unipotentProduct v
  rw [hv]
  simp [unipotentProduct]

/-- The fixed root elements include a noncommuting B–E pair. -/
private theorem fixed_roots_noncommuting (ρ : Fin 6 → F ≃+ F)
    (hρ : ∀ i, Function.Involutive (ρ i)) :
    ∃ b e : F, ρ 1 b=b ∧ ρ 4 e=e ∧
      ¬ Commute (unipotentProduct (Pi.single 1 b))
        (unipotentProduct (Pi.single 4 e)) := by
  obtain ⟨b,hb,hbf⟩ := nonzero_fixed (ρ 1) (hρ 1)
  obtain ⟨e,he,hef⟩ := nonzero_fixed (ρ 4) (hρ 4)
  refine ⟨b,e,hbf,hef,?_⟩
  intro hc
  have hh := congrFun (unipotentProduct_injective
    ((unipotentProduct_mul _ _).symm.trans (hc.eq.trans (unipotentProduct_mul _ _)))) 0
  simp [unipotentProductParameters] at hh
  exact he (hh.resolve_left hb)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2OuterGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2OuterGeometry
variable {G : Type*} [Group G]
variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
private theorem root_action_involutive
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (t : G) (ht : t^2=1) (ρ : Fin 6 → F ≃+ F)
    (ha : ∀ v : Fin 6 → F,
      t * f ⟨unipotentProduct v,borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem v))⟩ * t⁻¹ =
      f ⟨unipotentProduct (fun i => ρ i (v i)),
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩) :
    ∀ i, Function.Involutive (ρ i) := by
  intro i x
  have hh := ha (fun j => ρ j x)
  rw [←ha (fun _ => x)] at hh
  have htw (y : G) : t*(t*y*t⁻¹)*t⁻¹=y := by
    calc
      _ = (t*t)*y*(t*t)⁻¹ := by group
      _ = t^2*y*(t^2)⁻¹ := by rw [pow_two]
      _ = y := by rw [ht]; simp
  rw [htw] at hh
  have heq : (⟨unipotentProduct (fun _ : Fin 6 => x),
      borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩ : parabolic₁ (F := F)) =
      ⟨unipotentProduct (fun j => ρ j (ρ j x)),
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩ := hf hh
  have heq' : unipotentProduct (fun _ : Fin 6 => x) =
      unipotentProduct (fun j => ρ j (ρ j x)) := congrArg Subtype.val heq
  exact (congrFun (unipotentProduct_injective heq') i).symm

omit [CharP F 2] in
private theorem fixed_root_mem
    (f : parabolic₁ (F := F) →* G) (S E : Subgroup G)
    (hS : (unipotent.subgroupOf parabolic₁).map f=S)
    (t : G) (hSE : S ⊓ centralizer ({t} : Set G) ≤ E)
    (ρ : Fin 6 → F ≃+ F)
    (ha : ∀ v : Fin 6 → F,
      t * f ⟨unipotentProduct v,borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem v))⟩ * t⁻¹ =
      f ⟨unipotentProduct (fun i => ρ i (v i)),
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩)
    (i : Fin 6) (x : F) (hx : ρ i x=x) :
    f ⟨unipotentProduct (Pi.single i x),
      borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩ ∈ E := by
  apply hSE
  constructor
  · rw [←hS]
    exact mem_map_of_mem f (unipotentProduct_mem _)
  · apply mem_centralizer_singleton_iff.mpr
    apply Eq.symm
    apply mul_inv_eq_iff_eq_mul.mp
    have he : (fun j => ρ j ((Pi.single i x : Fin 6 → F) j)) = Pi.single i x := by
      funext j
      by_cases hji : j=i
      · subst j; simp [hx]
      · simp [hji]
    simpa only [he] using ha (Pi.single i x)

/-- The same root marking puts the source centralizer of E in the highest
root and proves E nonabelian, whenever E contains C_S(t). -/
private theorem fixed_roots_transport
    (f : parabolic₁ (F := F) →* G) (hf : Function.Injective f)
    (S E : Subgroup G) (hS : (unipotent.subgroupOf parabolic₁).map f=S)
    (t : G) (ht : t^2=1) (hSE : S ⊓ centralizer ({t} : Set G) ≤ E)
    (ρ : Fin 6 → F ≃+ F)
    (ha : ∀ v : Fin 6 → F,
      t * f ⟨unipotentProduct v,borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem v))⟩ * t⁻¹ =
      f ⟨unipotentProduct (fun i => ρ i (v i)),
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩) :
    S ⊓ centralizer (E : Set G) ≤ (highestRoot.subgroupOf parabolic₁).map f ∧
      commutator E ≠ ⊥ := by
  have hρ := root_action_involutive f hf t ht ρ ha
  have hmem := fixed_root_mem f S E hS t hSE ρ ha
  constructor
  · rintro x ⟨hx,hc⟩
    rw [←hS] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hz : y.val ∈ highestRoot (F := F) := by
      apply centralizer_fixed_roots ρ hρ y.val hy
      intro i u hu
      apply Commute.symm
      have hh := hc _ (hmem i u hu)
      have hh' : (⟨unipotentProduct (Pi.single i u),
          borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩ : parabolic₁ (F := F))*y =
          y*⟨unipotentProduct (Pi.single i u),
            borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩ := by
        apply hf
        rw [map_mul,map_mul]
        exact hh
      exact congrArg Subtype.val hh'
    exact mem_map_of_mem f hz
  · intro hbot
    let : IsMulCommutative E := (commutator_eq_bot_iff E).mp hbot
    obtain ⟨b,e,hb,he,hne⟩ := fixed_roots_noncommuting ρ hρ
    have hh := congrArg Subtype.val (mul_comm'
      (⟨_,hmem 1 b hb⟩ : E) (⟨_,hmem 4 e he⟩ : E))
    have hh' : (⟨unipotentProduct (Pi.single 1 b),
        borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩ : parabolic₁ (F := F))*
        ⟨unipotentProduct (Pi.single 4 e),borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩ =
        ⟨unipotentProduct (Pi.single 4 e),borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩*
        ⟨unipotentProduct (Pi.single 1 b),borel_le_parabolic₁ (mem_sup_left (unipotentProduct_mem _))⟩ := by
      apply hf
      rw [map_mul,map_mul]
      exact hh
    exact hne (congrArg Subtype.val hh')

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2OuterGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- The characteristic central-derived subgroup of the original torus
involution's Sylow centralizer is nontrivial and lies in Z(O²(H)). Its full
ambient normalizer therefore lies in the original right normalizer. -/
theorem Preparation.g2_outer_centralizer_normalizer
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2) (htD : t.val ∈ normalizer (D : Set G)) :
    let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
    let Z := (center E ⊓ commutator E).map E.subtype
    Z ≠ ⊥ ∧ Z ≤ (center (residual H)).map (residual H).subtype ∧
      normalizer (E : Set G) ≤ normalizer (residual H : Set G) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic₁ (F := F) →* G := P.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp e.right.symm.injective
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  let Z := (center E ⊓ commutator E).map E.subtype
  have hS := source_g2_inverse_sylow_image d h hH.1.1.2 e
  obtain ⟨ρ,hρ⟩ := d.g2_torus_normalizer_root_action h hH.1.1.2 hp F e hD hmark t htD
  have ht : t.val^2=1 := by
    exact congrArg Subtype.val ((orderOf_eq_prime_iff.mp ht2).1)
  have hgeom := G2OuterGeometry.fixed_roots_transport f hf (sourceS L H) E hS t.val ht
    (inf_le_inf_right _ (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)) ρ hρ
  have hs := d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)
  obtain ⟨b⟩ := hs.2.2.1
  let eR : (residual H ⧸ pCore 2 (residual H)) ≃* Theory.PSL2.Group F :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans local₁CoreQuotientEquivPSL
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : CommGroup (F ≃+* F) := IsCyclic.commGroup
  let χ := (residualSylowFieldAction hH.1.1.2 eR).comp (inclusion (show E ≤ T from inf_le_left))
  have hder : (commutator E).map E.subtype ≤ sourceS L H := by
    rintro _ ⟨x,hx,rfl⟩
    have hh : inclusion (show E ≤ T from inf_le_left) x ∈
        (residualSylowFieldAction hH.1.1.2 eR).ker :=
      Abelianization.commutator_subset_ker χ hx
    rw [d.residual_sylow_field_kernel h hH.1.1.2 hs.2.2.2.2 eR] at hh
    exact hh
  have htop : Z ≠ ⊥ := by
    let : Nontrivial (commutator E) := (nontrivial_iff_ne_bot _).mpr hgeom.2
    let : Fact (IsPGroup 2 E) := ⟨T.isPGroup'.to_le inf_le_left⟩
    obtain ⟨x,hx,hxc⟩ := exists_nontrivial_center_mem_normal (p := 2) (commutator E)
    intro hb
    have hz : x.val.val ∈ Z := mem_map_of_mem E.subtype ⟨hxc,x.property⟩
    rw [hb,mem_bot] at hz
    exact hx (Subtype.ext (Subtype.ext hz))
  have hJ : ((local₁ (F := F)).subgroupOf parabolic₁).map f=residual H := by
    have hr : (local₁ (F := F)).subgroupOf parabolic₁ = solvableResidual (parabolic₁ (F := F)) := by
      apply map_injective (parabolic₁ (F := F)).subtype_injective
      rw [map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),
        HigherFieldResiduals.parabolic₁_residual (show 2 < Nat.card F by
          rw [hs.1]; exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.exponent)]
    rw [hr,show f=P.subtype.comp e.right.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.symm.toMonoidHom e.right.symm.surjective]
    exact d.parabolic_residuals h hH.1.1.2 hp 1
  have hroot : (highestRoot.subgroupOf parabolic₁).map f ≤
      (center (residual H)).map (residual H).subtype := by
    let J := (local₁ (F := F)).subgroupOf parabolic₁
    have hZ : ((center J).map J.subtype).map f =
        (center (residual H)).map (residual H).subtype := by
      rw [map_subgroup_center_eq f hf,hJ]
    have hZm : ((center J).map J.subtype).map (parabolic₁ (F := F)).subtype = highestRoot := by
      rw [map_subgroup_center_eq _ (parabolic₁ (F := F)).subtype_injective,
        map_subgroupOf_eq_of_le (le_sup_left.trans_eq local₁_sup_borel),RootPair.local_center]
    rw [←hZ]
    apply map_mono
    intro y hy
    have hm : y.val ∈ ((center J).map J.subtype).map (parabolic₁ (F := F)).subtype := hZm.symm ▸ hy
    obtain ⟨u,hu,he⟩ := hm
    exact (show u=y from Subtype.ext he) ▸ hu
  have hZ : Z ≤ (center (residual H)).map (residual H).subtype := by
    apply le_trans ?_ (hgeom.1.trans hroot)
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨hder (mem_map_of_mem E.subtype hx.2),mem_centralizer_iff.mpr (fun y hy =>
      congrArg Subtype.val (mem_center_iff.mp hx.1 ⟨y,hy⟩))⟩
  have hTI := d.g2_right_center_fusion h hH hp F (Or.inr ⟨e⟩)
  refine ⟨htop,hZ,?_⟩
  exact (normalizer_le_normalizer_characteristic_image E (center E ⊓ commutator E)).trans
    ((hTI.2.1.normalizer_le_of_ne_bot htop hZ).trans_eq hTI.2.2)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

private theorem normalizer_enlargement (E C : Subgroup G)
    (hEC : E ≤ C) (hE : IsPGroup 2 E)
    (hsmall : ∀ P : Sylow 2 C, Nat.card E < Nat.card P) :
    ∃ V : Subgroup G, IsPGroup 2 V ∧ E < V ∧ V ≤ C ∧
      V ≤ normalizer (E : Set G) := by
  obtain ⟨P,hP⟩ := (hE.comap_subtype (K := C)).exists_le_sylow
  let R := (P : Subgroup C).map C.subtype
  have hER : E ≤ R := by
    rw [←map_subgroupOf_eq_of_le hEC]
    exact map_mono hP
  have hR : IsPGroup 2 R := P.isPGroup'.map C.subtype
  let : Group.IsNilpotent R := hR.isNilpotent
  have hproper : E.subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top,Ne,subgroupOf_eq_top]
    intro hRE
    have hh := card_le_of_le hRE
    rw [card_map_of_injective C.subtype_injective] at hh
    exact (not_le_of_gt (hsmall P)) hh
  obtain ⟨u,huN,huE⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (E.subgroupOf R) hproper)
  let V := (normalizer (E.subgroupOf R : Set R)).map R.subtype
  have hEV : E ≤ V := by
    intro x hx
    exact ⟨⟨x,hER hx⟩,le_normalizer hx,rfl⟩
  refine ⟨V,(hR.to_subgroup _).map _,lt_of_le_of_ne hEV ?_,
    (map_subtype_le _).trans (map_subtype_le _),?_⟩
  · intro he
    have hu : u.val ∈ V := mem_map_of_mem R.subtype huN
    rw [←he] at hu
    exact huE hu
  · rw [←map_subgroupOf_eq_of_le hER]
    exact (E.subgroupOf R).le_normalizer_map R.subtype

/-- The ambient q⁴ lower bound forces a strict two-group enlargement of
C_T(t) inside the literal right-normalizer centralizer. This uses the full
ambient centralizer and its Sylow subgroup, not a Sylow claim inferred from
membership in T. Ruling out this local enlargement finishes F.4.38. -/
theorem Preparation.g2_outer_involution_local_enlargement
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val ∈ D ↔ (e.middle b).val ∈ splitTorus)
    (t : T) (ht2 : orderOf t=2) (htS : t.val ∉ sourceS L H)
    (htD : t.val ∈ normalizer (D : Set G)) :
    let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
    ∃ V : Subgroup G, IsPGroup 2 V ∧ E < V ∧
      V ≤ normalizer (residual H : Set G) ⊓ centralizer ({t.val} : Set G) ∧
      V ≤ normalizer (E : Set G) := by
  let E := (T : Subgroup G) ⊓ centralizer ({t.val} : Set G)
  have hn := (d.g2_outer_centralizer_normalizer h hH hp F e hD hmark t ht2 htD).2.2
  have hu := (d.g2_outer_involution_centralizer_lt h hH hp F e hD hmark t ht2 htS htD).2
  have hl := d.g2_involution_centralizer_sylow_lower_bound h hH hp F (Or.inr ⟨e⟩)
    t.val ((Subgroup.orderOf_coe t).trans ht2)
  obtain ⟨V,hV,hEV,hVC,hVN⟩ := normalizer_enlargement E (centralizer ({t.val} : Set G))
    inf_le_right (T.isPGroup'.to_le inf_le_left) (fun P => hu.trans_le (hl P))
  exact ⟨V,hV,hEV,le_inf (hVN.trans hn) hVC,hVN⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

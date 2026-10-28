module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAction
public import Theory.Representation.BinaryConjugationCoordinates
public import Theory.Representation.BinaryPermutation.SixCorePlaneMovement
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SecondFlag

/-!
# The rank-three actor in the original plane radical

The actual augmentation action sends N_LT(V₂) into the stabilizer of its
marked natural-quotient plane and contains that stabilizer's even part.
Relative normality therefore places its two-core image inside a conjugate
of the cube of three disjoint swaps. An actor of centralizer index eight
fills this cube. Its fixed vectors are products of actual commutators by
the displacement calculation in SixCorePlaneMovement.

The resulting inclusion C_V(A) ≤ [V,A] also puts C_V(L) in [V,A].
MixedLinearCommutator applies this to A=V₀ᵍ in the original pair. The
five-dimensional core, its coordinate map and the full normalizer action
are retained; no action on a different quotient module is substituted.
Source: Aschbacher--Smith 13.4.15, printed p.912, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Theory.GroupTheory Chapter12.Section02 BinaryConjugationCoordinates
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem normalizes_preimage_iff
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hn : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (q : normalizer (L : Set G) →* Equiv.Perm (Fin 6))
    (hq : ∀ (x : normalizer (L : Set G)) (v : V),
      (m.coordinate (V.normalizerMonoidHom (inclusion hn x) v)).toAdd =
        coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd)
    (W : Submodule (ZMod 2) (natural (Fin 6))) (x : normalizer (L : Set G)) :
    x.val ∈ normalizer (m.naturalPreimage W : Set G) ↔ q x ∈ flagStabilizer W := by
  have he (v : V) :
      coreToNatural (Fin 6) (m.coordinate (V.normalizerMonoidHom (inclusion hn x) v)).toAdd =
        naturalRepresentation (Fin 6) (q x) (coreToNatural (Fin 6) (m.coordinate v).toAdd) := by
    rw [hq,coreToNatural_equivariant]
  constructor
  · intro hx w
    obtain ⟨c,rfl⟩ := coreToNatural_surjective w
    obtain ⟨v,hv⟩ := m.coordinate.surjective (Multiplicative.ofAdd c)
    have hc : (m.coordinate v).toAdd = c := congrArg Multiplicative.toAdd hv
    rw [←hc,←he,←m.mem_naturalPreimage,←m.mem_naturalPreimage]
    exact ((mem_normalizer_iff.mp hx) v.val).symm
  · intro hx
    apply mem_normalizer_iff.mpr
    intro a
    by_cases ha : a ∈ V
    · let v : V := ⟨a,ha⟩
      have hh := hx (coreToNatural (Fin 6) (m.coordinate v).toAdd)
      rw [←he,←m.mem_naturalPreimage,←m.mem_naturalPreimage] at hh
      exact hh.symm
    · have ha' : x.val*a*x.val⁻¹ ∉ V :=
        fun hh => ha (((mem_normalizer_iff.mp (hn x.property)) a).mpr hh)
      exact iff_of_false (fun hh => ha (m.naturalPreimage_le W hh))
        (fun hh => ha' (m.naturalPreimage_le W hh))

/-- The literal second-parabolic radical acts inside the conjugate cube of
three disjoint swaps. The marking retains the full normalizer action. -/
theorem original_plane_radical_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let hBN : B ≤ normalizer (L : Set G) :=
      inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
    ∃ (q : normalizer (L : Set G) →* Equiv.Perm (Fin 6))
      (a : alternatingGroup (Fin 6)),
      (∀ (x : normalizer (L : Set G)) (v : V),
        (m.coordinate (V.normalizerMonoidHom
          ⟨x.val,normalizer_component_le_module h structural D m x.property⟩ v)).toAdd =
          coreRepresentation (Fin 6) (q x) (m.coordinate v).toAdd) ∧
      (pCore 2 B).map (q.comp (inclusion hBN)) ≤
        Theory.SpecificGroups.SymmetricSix.BinaryFlags.D.map (MulAut.conj a.val).toMonoidHom := by
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  have hBN : B ≤ normalizer (L : Set G) :=
    inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨q,hq,hqL,_⟩ := exists_core_normalizer_permutation D m hn
  let f := q.comp (inclusion hBN)
  let F := flagStabilizer W
  have hF : f.range ≤ F := by
    rintro x ⟨b,rfl⟩
    exact (normalizes_preimage_iff D m hn q hq W (inclusion hBN b)).mp b.property.2
  have hEven : F ⊓ alternatingGroup (Fin 6) ≤ f.range := by
    rw [←m.naturalPreimage_normalizer_image W]
    rintro x ⟨l,hl,rfl⟩
    refine ⟨⟨l.val,⟨mem_sup_left l.property,hl.2⟩⟩,?_⟩
    exact hqL l
  have hnormal : F ≤ normalizer (f.range : Set (Equiv.Perm (Fin 6))) := by
    apply (normal_subgroupOf_iff_le_normalizer hF).mp
    constructor
    intro n hn g
    change (g : Equiv.Perm (Fin 6)) * (n : Equiv.Perm (Fin 6)) * (g : Equiv.Perm (Fin 6))⁻¹ ∈ f.range
    change n.val ∈ f.range at hn
    have hc : ⁅g.val,n.val⁆ ∈ f.range := hEven ⟨
      F.mul_mem (F.mul_mem (F.mul_mem g.property (hF hn)) (F.inv_mem g.property))
        (F.inv_mem (hF hn)),by
      change Equiv.Perm.sign ⁅g.val,n.val⁆ = 1
      simp [commutatorElement_def,mul_assoc,mul_left_comm,mul_comm]⟩
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]
      using f.range.mul_mem hc hn
  have hcore : (pCore 2 B).map f ≤ f.range.pCoreIn 2 := by
    have hsmall : (pCore 2 B).map f.rangeRestrict ≤ pCore 2 f.range :=
      le_sSup ⟨Subgroup.Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective,
        pCore_isPGroup.map f.rangeRestrict⟩
    have hh := map_mono (f := f.range.subtype) hsmall
    rw [map_map] at hh
    exact hh
  obtain ⟨a,ha⟩ := m.natural_plane_alignment W hW hT
  refine ⟨q,a,hq,?_⟩
  have hc := hcore.trans (pCoreIn_mono_of_normalizes hF hnormal)
  have hFe : F.pCoreIn 2 = Theory.SpecificGroups.SymmetricSix.BinaryFlags.D.map
      (MulAut.conj a.val).toMonoidHom := by
    dsimp [F]
    rw [ha,flagStabilizer_move,flagStabilizer_plane,
      ←map_pCoreIn_of_injective 2 _ _ (MulAut.conj a.val).injective,H2_core_eq_D]
    rfl
  exact hc.trans_eq hFe

omit [Finite G] in
/-- Every fixed element is a commutator product when the actor image is the
full syntheme radical. This is a statement about the literal ambient subgroups. -/
private theorem fixed_le_commutator_of_cube_image
    (A : Subgroup G) (hAV : A ≤ normalizer (V : Set G))
    (e : V ≃* Multiplicative (core (Fin 6)))
    (f : A →* Equiv.Perm (Fin 6))
    (he : ∀ (a : A) (v : V),
      (e (V.normalizerMonoidHom ⟨a.val,hAV a.property⟩ v)).toAdd =
        coreRepresentation (Fin 6) (f a) (e v).toAdd)
    (g : Equiv.Perm (Fin 6))
    (hf : f.range = Theory.SpecificGroups.SymmetricSix.BinaryFlags.D.map
      (MulAut.conj g).toMonoidHom) :
    V ⊓ centralizer (A : Set G) ≤ ⁅V,A⁆ := by
  let j := V.subtype.comp e.symm.toMonoidHom
  have hdisp (a : A) (w : core (Fin 6)) :
      j (Multiplicative.ofAdd (coreRepresentation (Fin 6) (f a) w - w)) ∈ ⁅V,A⁆ := by
    let v := e.symm (Multiplicative.ofAdd w)
    have hc := he a v
    have hcomm : j (Multiplicative.ofAdd (coreRepresentation (Fin 6) (f a) w - w)) =
        ⁅a.val,v.val⁆ := by
      have hc' : e (V.normalizerMonoidHom ⟨a.val,hAV a.property⟩ v) =
          Multiplicative.ofAdd (coreRepresentation (Fin 6) (f a) w) := by
        apply Multiplicative.toAdd.injective
        simpa only [v,e.apply_symm_apply,toAdd_ofAdd] using hc
      rw [ofAdd_sub,div_eq_mul_inv]
      change (e.symm (Multiplicative.ofAdd (coreRepresentation (Fin 6) (f a) w) *
        (Multiplicative.ofAdd w)⁻¹)).val = _
      rw [map_mul,map_inv,←hc',e.symm_apply_apply]
      rfl
    rw [hcomm,commutator_comm]
    exact commutator_mem_commutator a.property v.property
  intro v hv
  let w := (e ⟨v,hv.1⟩).toAdd
  have hw : ∀ a ∈ Theory.SpecificGroups.SymmetricSix.BinaryFlags.D.map
      (MulAut.conj g).toMonoidHom, coreRepresentation (Fin 6) a w = w := by
    intro a ha
    rw [←hf] at ha
    obtain ⟨b,rfl⟩ := ha
    rw [←he]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hv.2 b.val b.property)
  obtain ⟨a,ha,b,hb,c,hc,x,y,z,hxyz⟩ :=
    SixCorePlaneMovement.fixed_is_sum_of_conjugate_displacements g w hw
  rw [←hf] at ha hb hc
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨b,rfl⟩ := hb
  obtain ⟨c,rfl⟩ := hc
  have hvj : j (Multiplicative.ofAdd w) = v :=
    congrArg Subtype.val (e.symm_apply_apply ⟨v,hv.1⟩)
  rw [←hvj,hxyz]
  change j ((Multiplicative.ofAdd _) * (Multiplicative.ofAdd _) *
    (Multiplicative.ofAdd _)) ∈ _
  rw [map_mul,map_mul]
  exact mul_mem (mul_mem (hdisp a x) (hdisp b y)) (hdisp c z)

/-- Rank-three action by a subgroup of the original second radical forces
its whole fixed subgroup into its commutator, and hence contains C_V(L). -/
theorem original_plane_actor_fixed_le_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (A : Subgroup G)
    (hA : A ≤ ((L ⊔ (T : Subgroup G)) ⊓ normalizer
      (m.naturalPreimage W : Set G) : Subgroup G).pCoreIn 2)
    (hi : (centralizer (V : Set G)).relIndex A = 8) :
    V ⊓ centralizer (A : Set G) ≤ ⁅V,A⁆ ∧
      V ⊓ centralizer (L : Set G) ≤ ⁅V,A⁆ := by
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  have hBN : B ≤ normalizer (L : Set G) :=
    inf_le_left.trans (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hAN := hA.trans ((pCoreIn_le 2 B).trans hBN)
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨q,a,hq,hcore⟩ := original_plane_radical_image h structural D m W hW hT
  let f := q.comp (inclusion hAN)
  have hf : f.range ≤ Theory.SpecificGroups.SymmetricSix.BinaryFlags.D.map
      (MulAut.conj a.val).toMonoidHom := by
    rintro x ⟨b,rfl⟩
    obtain ⟨r,hr,her⟩ := hA b.property
    apply hcore
    refine ⟨r,hr,?_⟩
    change q ⟨r.val,_⟩ = q ⟨b.val,_⟩
    congr 1
    exact Subtype.ext her
  have hc := model_card_range A V (hAN.trans hn) (coreRepresentation (Fin 6))
    SixCoreNormalizer.action_injective f m.coordinate (fun b v => hq (inclusion hAN b) v)
  rw [inf_relIndex_left,hi] at hc
  have heq : f.range = Theory.SpecificGroups.SymmetricSix.BinaryFlags.D.map
      (MulAut.conj a.val).toMonoidHom :=
    eq_of_le_of_card_ge hf (by rw [hc,card_map_of_injective (MulAut.conj a.val).injective,D_card])
  have hm := fixed_le_commutator_of_cube_image A (hAN.trans hn) m.coordinate f
    (fun b v => hq (inclusion hAN b) v) a.val heq
  refine ⟨hm,(le_inf inf_le_left ?_).trans hm⟩
  exact le_centralizer_iff.mp
    (hAN.trans (normalizer_component_le_fixed_centralizer h structural D m))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

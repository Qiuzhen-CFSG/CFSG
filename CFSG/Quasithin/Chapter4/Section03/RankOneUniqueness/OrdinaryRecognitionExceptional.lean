module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionPlacement
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryModel
public import Theory.GroupTheory.PCoreImage

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import Theory.AtlasPort.LinearGroups.G2.LongLocalFixer
public import Theory.AtlasPort.LinearGroups.G2.ShortLocalCoreCenter
public import Theory.SpecificGroups.Triality.ArmsLocalCoreCenter

/-!
# Exceptional rank-two exclusions for the original ordinary configuration

The full source module W is nonzero and fully moved by the original L,
and lies in Z(O₂(L)). In every actual central-quotient model of K its
image therefore witnesses that Z(O₂(L-image)) is not central in L-image.
The two-group kernel is retained in this transport; W is never replaced
by the chosen Chapter 12 module.

Full-Sylow local placement now excludes both G₂ parabolic residuals:
the short residual centralizes its core center, while the long residual
has trivial automorphism fixer, contradicting the actual R₀ involution.
For genuine triality the arms residual is excluded by the same full-module
argument, and the central residual by its involutory fixer theorem.
These exclusions apply to every central cover over fields larger than two.

The remaining source recognition and construction of OrdinarySymplecticMarking
belong to qt-d-1222-rankone-ordinary-symplectic-marking. In particular this
family does not assume or assert the local-pair alternatives of C.3.1.
Source: Aschbacher--Smith C.2.8 and C.3.1--5, printed pp.147--151,
and the ordinary-component argument in 4.3.6, printed p.614.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
namespace SourceConfiguration

/-- The full source module, inside the original L, is nonzero, fully moved,
and lies in the center of its actual two-core. -/
theorem ordinaryModule_local_data (c : SourceConfiguration T L) :
    let A := c.ordinaryModule.subgroupOf L
    A ≠ ⊥ ∧ ⁅A,(⊤ : Subgroup L)⁆ = A ∧
      A ≤ (center (pCore 2 L)).map (pCore 2 L).subtype := by
  let W := c.ordinaryModule
  let A := W.subgroupOf L
  have hWL : W ≤ L := by simpa only [c.ordinary_span_eq] using c.c28.module_le
  have hm : W = ⁅W,L⁆ := by simpa only [c.ordinary_span_eq] using c.c28.module_commutator
  have hmap : A.map L.subtype = W := map_subgroupOf_eq_of_le hWL
  have hmove : ⁅A,(⊤ : Subgroup L)⁆ = A := by
    apply map_injective L.subtype_injective
    rw [map_commutator,hmap,←MonoidHom.range_eq_map,range_subtype]
    exact hm.symm
  have hA : A.Normal := by
    apply normal_subgroupOf_of_le_normalizer
    rw [hm]
    exact normalizer_commutator_ge_right _ _
  have hAp : IsPGroup 2 A := c.c28.module_elementary.isPGroup.comap_subtype
  have hAcore : A ≤ pCore 2 L := le_sSup ⟨hA,hAp⟩
  have hLR : L.pCoreIn 2 ≤ c.I.pCoreIn 2 := by
    apply pCoreIn_mono_of_normalizes c.le_I
    rw [c.I_eq]
    exact sup_le L.le_normalizer (c.c28.radical_le.trans inf_le_right)
  refine ⟨?_,hmove,?_⟩
  · intro hz
    have hh := congrArg (map L.subtype) hz
    rw [hmap,Subgroup.map_bot] at hh
    exact c.c28.module_nontrivial hh
  · intro w hw
    refine ⟨⟨w,hAcore hw⟩,mem_center_iff.mpr ?_,rfl⟩
    intro r
    obtain ⟨z,hz,he⟩ := c.c28.module_le_center_radical hw
    have hc := congrArg (fun x : c.I.pCoreIn 2 => (x : G))
      (mem_center_iff.mp hz ⟨(r : L),hLR (mem_map_of_mem L.subtype r.property)⟩)
    apply Subtype.ext
    apply Subtype.ext
    change (r : G) * (w : G) = (w : G) * (r : G)
    change (r : G) * (z : G) = (z : G) * (r : G) at hc
    change (z : G) = (w : G) at he
    rwa [he] at hc

/-- In every actual central-quotient model of K, the image of the original L
has a noncentral core center. The full source module supplies the obstruction. -/
theorem ordinary_model_core_center_not_central (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K) {S : Type*} [Group S] [Finite S]
    (e : (c.K ⧸ center c.K) ≃* S) :
    let B := c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))
    ¬ (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let B := c.ordinaryLocal.map q
  change ¬ (center (pCore 2 B)).map (pCore 2 B).subtype ≤ center B
  let k : L ≃* c.ordinaryLocal := c.ordinaryLocalEquiv.symm
  let f : L →* B := (q.subgroupMap c.ordinaryLocal).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective c.ordinaryLocal).comp k.surjective
  have hqker : q.ker = center c.K := by
    ext x
    change e (QuotientGroup.mk' (center c.K) x) = 1 ↔ x ∈ center c.K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    have hz : (k l : c.K) ∈ center c.K := by
      rw [←hqker]
      exact hh
    apply mem_center_iff.mpr
    intro m
    apply k.injective
    simpa only [map_mul] using
      (Subtype.ext (mem_center_iff.mp hz (k m : c.K)) : k m * k l = k l * k m)
  have hkp : IsPGroup 2 f.ker := by
    have hp : IsPGroup 2 q.ker := by
      rw [hqker,c.ordinary_center_eq_twoCore ho]
      exact pCore_isPGroup
    have hker : f.ker = q.ker.comap (c.ordinaryLocal.subtype.comp k.toMonoidHom) := by
      ext x
      exact Subtype.ext_iff
    rw [hker]
    exact hp.comap_of_injective _ (c.ordinaryLocal.subtype_injective.comp k.injective)
  have hcore : (pCore 2 L).map f = pCore 2 B := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hkp,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  let A := c.ordinaryModule.subgroupOf L
  obtain ⟨hne,hmove,hcentral⟩ := c.ordinaryModule_local_data
  let N := A.map f
  have hNcore : N ≤ pCore 2 B := by
    rw [←hcore]
    exact map_mono (hcentral.trans (map_subtype_le _))
  have hNc : N ≤ centralizer (pCore 2 B : Set B) := by
    rintro _ ⟨w,hw,rfl⟩ r hr
    rw [←hcore] at hr
    obtain ⟨r,hr,rfl⟩ := hr
    obtain ⟨z,hz,rfl⟩ := hcentral hw
    have hh : r * (z : L) = (z : L) * r :=
      congrArg Subtype.val (mem_center_iff.mp hz ⟨r,hr⟩)
    change f r * f (z : L) = f (z : L) * f r
    simpa only [map_mul] using congrArg f hh
  have hNmove : ⁅N,(⊤ : Subgroup B)⁆ = N := by
    rw [show (⊤ : Subgroup B) = (⊤ : Subgroup L).map f from
      (map_top_of_surjective _ hf).symm,←map_commutator,hmove]
  intro hc
  have hNZ : N ≤ center B := by
    intro n hn
    exact hc ⟨⟨n,hNcore hn⟩,
      mem_center_iff.mpr (fun r => Subtype.ext (hNc hn r r.property)),rfl⟩
  have hNzero : N = ⊥ := hNmove.symm.trans
    (commutator_top_right_eq_bot_iff_le_center.mpr hNZ)
  have hAZ : A ≤ center L := ((map_eq_bot_iff A).mp hNzero).trans hk
  exact hne (hmove.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr hAZ))

/-- The two-core of the image of the original L is nontrivial. -/
theorem ordinary_model_local_core_ne_bot (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K) {S : Type*} [Group S] [Finite S]
    (e : (c.K ⧸ center c.K) ≃* S) :
    pCore 2 (c.ordinaryLocal.map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))) ≠ ⊥ := by
  intro hz
  apply c.ordinary_model_core_center_not_central ho e
  rintro _ ⟨z,_,rfl⟩
  have hz' : (z : c.ordinaryLocal.map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))) = 1 :=
    mem_bot.mp (hz ▸ z.property)
  change (z : c.ordinaryLocal.map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))) ∈ center _
  rw [hz']
  exact one_mem _

/-- Both literal G₂ parabolic rows are excluded from the original ordinary
configuration, for every field larger than two and every central cover. -/
theorem ordinary_no_g2 (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (e : (c.K ⧸ center c.K) ≃* Atlas.G2.Model F) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  obtain ⟨P,_,hlocal,hproper⟩ := c.ordinary_model_local_data D ho e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center c.K)))
  obtain ⟨g,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2.local_placement
    hq S (c.ordinaryLocal.map f) hlocal hproper
  let e' := e.trans (MulAut.conj g)
  have he : e'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext; rfl
  have hm : c.ordinaryLocal.map (e'.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) =
      Atlas.G2.LieParabolicSetup.local₁ ∨
      c.ordinaryLocal.map (e'.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) =
      Atlas.G2.LieParabolicSetup.local₂ := by
    simpa only [f,map_map,he,MonoidHom.comp_assoc] using hg
  rcases hm with hm | hm
  · have hc := c.ordinary_model_core_center_not_central ho e'
    dsimp only at hc
    rw [hm] at hc
    exact hc Atlas.G2.LieParabolicSetup.local₁_core_center_le_center
  · obtain ⟨a,hao,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e'
    rw [hm] at hfix
    have ha := Atlas.G2.LieParabolicSetup.local₂_fixer_eq_one hq a hfix
    simp only [ha,orderOf_one] at hao
    omega

/-- Both genuine triality parabolic rows are excluded for fields larger than
two. The core and local markings are derived from the same original L and Sylow. -/
theorem ordinary_no_triality_large (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    (n : ℕ) (hn : 0 < n) (hq : 2 < 2 ^ n)
    (e : (c.K ⧸ center c.K) ≃* Triality.Standard.BinaryCarrier n hn) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  obtain ⟨P,_,hlocal,_⟩ := c.ordinary_model_local_data D ho e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center c.K)))
  obtain ⟨g,a,hg⟩ := ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality.local_placement
    n hn hq S (c.ordinaryLocal.map f) hlocal (c.ordinary_model_local_core_ne_bot ho e)
  let e' := e.trans (MulAut.conj g)
  have he : e'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext; rfl
  have hm : c.ordinaryLocal.map (e'.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) =
      Triality.Standard.Parabolics.localFactor (Triality.Standard.binaryParameters n hn) a := by
    simpa only [f,map_map,he,MonoidHom.comp_assoc] using hg
  cases a with
  | arms =>
    have hc := c.ordinary_model_core_center_not_central ho e'
    dsimp only at hc
    rw [hm] at hc
    exact hc (Triality.Standard.Parabolics.arms_core_center_le_center _ rfl)
  | central => exact c.ordinary_no_triality_central_marking D ho n hn e' hm

end SourceConfiguration
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

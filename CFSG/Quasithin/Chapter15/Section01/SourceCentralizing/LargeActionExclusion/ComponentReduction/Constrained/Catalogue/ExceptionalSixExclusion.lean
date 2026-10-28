module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ExceptionalSixSeed
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.FieldModel
public import Theory.Representation.HexacodeAction.NormalOvergroup
public import Theory.Representation.HexacodeAction.ThompsonOffenders
-- The finite witness below deliberately uses the internal Sylow word bodies.
-- Keep this computational coupling private; no upstream public boundary changes.
import all Theory.Representation.HexacodeAction.ThompsonOffenders

/-!
# Excluding the exceptional cubic A₆ block

The original central-involution seed lies in the actual six-dimensional
hexacode module of an exceptional block. Its point centralizer cannot
normalize the unique best offender in the same Sylow two-group: the explicit
word `hexLift 0 * hexLift 1` fixes every Sylow-fixed vector and moves the
plane four-group. The finite witness is checked by kernel reduction.

Transport the full normal-overgroup action to the hexacode, preserving U(K)
and the original two-core quotient, including its cubic center. Because the
seed centralizer lies in M_Z, it normalizes the literal Q₁. The offender
calculation therefore puts J(Q₁) in the action kernel and then in O₂(KQ₁),
contradicting the actual Thompson escape in C.2.7. Both original source primes
and the later exchanged application retain the same component and quotient.

This removes the cubic branch from the selected constrained catalogue.
The independently owned whole-core A₆ reconstruction and genuine earlier
15.1.14 residual input remain explicit in that catalogue theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.1.20(2), printed pp.1094–1095, especially the final paragraph on p.1095;
B.4.2(8) and C.2.7. The imported hexacode coordinates and monomial lifts are
the licensed ATLAS constructions by Gerald Höhn and contributors; see
`LICENSES/ATLAS.txt` and `Theory.AtlasPort.OtherSporadic.Codes`.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Atlas.Codes Representation.Hexacode Representation.Hexacode.SixDimensional
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ExceptionalSixOffenders
open ChapterC
open Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix
variable {G : Type*} [Group G] (X : Subgroup G) [X.Normal]

private noncomputable def blockAction [IsElementaryAbelian 2 (blockU X)] :
    Representation (ZMod 2) G (Additive (blockU X)) where
  toFun g := ((MulAut.characteristic (blockU X)).comp MulAut.conjNormal g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (((MulAut.characteristic (blockU X)).comp MulAut.conjNormal 1) v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (((MulAut.characteristic (blockU X)).comp MulAut.conjNormal (a*b)) v.toMul) = _
    rw [map_mul]
    rfl

/-- The entire normal overgroup acts in the actual full hexacode model,
with its original two-core quotient and original U retained. -/
private theorem normal_action (hb : IsExceptionalAhat6Block X) :
    letI := hb.1.elementary
    ∃ (c : (X ⧸ pCore 2 X) ≃* HexEvenAutomorphisms)
      (E : Additive (blockU X) ≃ₗ[ZMod 2] hexacode)
      (f : G →* HexAutomorphisms),
      (∀ x : X, f x = (c (QuotientGroup.mk' (pCore 2 X) x)).val) ∧
      (∀ g u, E (Additive.ofMul
        (MulAut.characteristic (blockU X) (MulAut.conjNormal g) u)) =
        action (f g) (E (Additive.ofMul u))) ∧
      X.map f = hexSign.ker ∧
      (f.comp X.subtype).ker = pCore 2 X ∧
      f.ker = centralizer ((blockU X).map X.subtype : Set G) := by
  let := hb.1.elementary
  obtain ⟨m⟩ := nonempty_hexacodeModel hb
  let ρ := blockAction X
  let a := coordinateAction ρ m.coordinates
  have hρ (x : X) (v : Additive (blockU X)) :
      ρ x v = binaryAction hb (QuotientGroup.mk' (pCore 2 X) x) v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact (congrArg (fun y : X => (y : G)) (binaryAction_apply hb x v)).symm
  have ha (x : X) : a x = hexAction (m.quotientIso (QuotientGroup.mk' (pCore 2 X) x)).val := by
    apply LinearEquiv.ext
    intro v
    change m.coordinates (ρ x (m.coordinates.symm v)) = _
    rw [hρ,m.intertwining,m.coordinates.apply_symm_apply]
    rfl
  have himage : X.map a = evenBinaryImage := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨m.quotientIso (QuotientGroup.mk' (pCore 2 X) ⟨x,hx⟩),(ha ⟨x,hx⟩).symm⟩
    · rintro _ ⟨x,rfl⟩
      obtain ⟨k,hk⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 X)) x
      exact ⟨k,k.property,(ha k).trans (congrArg (fun y : HexEvenAutomorphisms => hexAction y.val) hk)⟩
  have hmem (g : G) : a g ∈ hexAction.range := by
    rw [←normalizer_evenBinaryImage,←himage]
    exact le_normalizer_map a ⟨g,by rw [X.normalizer_eq_top]; trivial,rfl⟩
  let j := a.codRestrict hexAction.range hmem
  let f := (MonoidHom.ofInjective hexAction_injective).symm.toMonoidHom.comp j
  have hf (g : G) : hexAction (f g) = a g :=
    MonoidHom.apply_ofInjective_symm hexAction_injective (j g)
  have hfx (x : X) : f x = (m.quotientIso (QuotientGroup.mk' (pCore 2 X) x)).val := by
    apply hexAction_injective
    rw [hf,ha]
  have hE (g : G) (u : blockU X) : m.coordinates (Additive.ofMul
        (MulAut.characteristic (blockU X) (MulAut.conjNormal g) u)) =
        action (f g) (m.coordinates (Additive.ofMul u)) := by
    have he := LinearEquiv.congr_fun (hf g) (m.coordinates (Additive.ofMul u))
    change action (f g) (m.coordinates (Additive.ofMul u)) =
      m.coordinates (ρ g (m.coordinates.symm (m.coordinates (Additive.ofMul u)))) at he
    rw [m.coordinates.symm_apply_apply] at he
    exact he.symm
  refine ⟨m.quotientIso,m.coordinates,f,hfx,hE,?_,?_,?_⟩
  · apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      rw [hfx ⟨x,hx⟩]
      exact (m.quotientIso (QuotientGroup.mk' (pCore 2 X) ⟨x,hx⟩)).property
    · intro g hg
      obtain ⟨x,hx⟩ := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 X)) ⟨g,hg⟩
      exact ⟨x,x.property,(hfx x).trans (congrArg Subtype.val hx)⟩
  · ext x
    change f x = 1 ↔ x ∈ pCore 2 X
    rw [hfx]
    constructor
    · intro hx
      apply (QuotientGroup.eq_one_iff (N := pCore 2 X) x).mp
      apply m.quotientIso.injective
      rw [map_one]
      exact Subtype.ext hx
    · intro hx
      have he : QuotientGroup.mk' (pCore 2 X) x = 1 :=
        (QuotientGroup.eq_one_iff (N := pCore 2 X) x).mpr hx
      rw [he,map_one]
      rfl
  · ext g
    constructor
    · intro hg u hu
      obtain ⟨v,hv,rfl⟩ := hu
      have he := hE g ⟨v,hv⟩
      rw [show f g = 1 from hg,map_one,Module.End.one_apply] at he
      have hh := congrArg (fun w : Additive (blockU X) => ((w.toMul : X) : G))
        (m.coordinates.injective he)
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hg
      change f g = 1
      apply Hexacode.action_injective
      apply LinearMap.ext
      intro v
      obtain ⟨u,rfl⟩ := m.coordinates.surjective v
      change action (f g) (m.coordinates (Additive.ofMul u.toMul)) = _
      rw [←hE g u.toMul]
      have he : MulAut.characteristic (blockU X) (MulAut.conjNormal g) u.toMul = u.toMul := by
        apply Subtype.ext
        apply Subtype.ext
        change g * ((u.toMul : X) : G) * g⁻¹ = u.toMul
        rw [←hg u.toMul (mem_map_of_mem X.subtype u.toMul.property),mul_inv_cancel_right]
      rw [he,map_one,Module.End.one_apply]
      rfl

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ExceptionalSixOffenders

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ExceptionalSixOffenders
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open Representation.Hexacode Representation.Hexacode.ThompsonOffenders

private theorem seed_mover : ∃ x : HexEvenAutomorphisms,
    (∀ w : hexacode, (∀ s ∈ SylowModel.sylowGroup, evenAction s w = w) →
      evenAction x w = w) ∧ x ∉ normalizer (SylowModel.planeGroup : Set _) := by
  set_option maxRecDepth 4096 in
  have hc : ∃ a b : Fin 5,
      (∀ p : Fin 3 → K,
        Monomial.act SylowModel.z.val.val (systematicEncoder p) = systematicEncoder p →
        Monomial.act SylowModel.s.val.val (systematicEncoder p) = systematicEncoder p →
        Monomial.act SylowModel.t.val.val (systematicEncoder p) = systematicEncoder p →
        Monomial.act (hexLift a * hexLift b).val (systematicEncoder p) = systematicEncoder p) ∧
      (∀ p : Fin 2 × Fin 2,
        hexCoordinateSixHom ((hexLift a * hexLift b) * SylowModel.t.val * (hexLift a * hexLift b)⁻¹) ≠
          hexCoordinateSixHom (SylowModel.planeWord p).val) := by
    refine ⟨0,1,?_,?_⟩ <;> decide +kernel
  obtain ⟨a,b,hfix,hesc⟩ := hc
  let x : HexEvenAutomorphisms := ⟨hexLift a * hexLift b,by simp⟩
  refine ⟨x,?_,?_⟩
  · intro w hw
    have hz := congrArg Subtype.val (hw SylowModel.z (by
      exact ⟨(1,0,0),by simp [SylowModel.word]⟩))
    have hs := congrArg Subtype.val (hw SylowModel.s (by
      exact ⟨(0,1,0),by simp [SylowModel.word]⟩))
    have ht := congrArg Subtype.val (hw SylowModel.t (by
      exact ⟨(0,0,1),by simp [SylowModel.word]⟩))
    have hh := hfix (hexProjection firstThree w)
    rw [systematic_reconstruct] at hh
    exact Subtype.ext (hh hz hs ht)
  · intro hn
    have ht : SylowModel.t ∈ SylowModel.planeGroup :=
      ⟨(0,1),by simp [SylowModel.planeWord,SylowModel.word]⟩
    obtain ⟨p,hp⟩ := (mem_normalizer_iff.mp hn _).mp ht
    exact hesc p (congrArg (fun g : HexEvenAutomorphisms => hexCoordinateSixHom g.val) hp).symm

/-- A Sylow-fixed point's stabilizer cannot normalize the hexacode offender.
The finite witness is in the other source parabolic. -/
private theorem point_not_normalizes_offender (S : Sylow 2 HexEvenAutomorphisms)
    (A : Subgroup HexEvenAutomorphisms) (hAS : A ≤ S)
    (hA : IsBestOffender evenAction A) (w : hexacode)
    (hw : ∀ s ∈ S, evenAction s w = w) :
    ¬ ∀ k : HexEvenAutomorphisms, evenAction k w = w →
      k ∈ normalizer (A : Set _) := by
  intro hn
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq HexEvenAutomorphisms S standardSylow
  have hs : (S : Subgroup HexEvenAutomorphisms).map (MulAut.conj g).toMonoidHom =
      SylowModel.sylowGroup := congrArg Sylow.toSubgroup hg
  have hA' := hA.map_conj evenAction g
  have he : A.map (MulAut.conj g).toMonoidHom = SylowModel.planeGroup := by
    exact (SylowModel.fourGroup_exhaustion _ hA'.1.2 (hs ▸ map_mono hAS)
      (bestOffender_dimensions _ hA').2.1).resolve_left
        (fun he => lineGroup_not_offender ((he ▸ hA').isOffender _))
  have hc (a b : HexEvenAutomorphisms) (v : hexacode) :
      evenAction (MulAut.conj a b) (evenAction a v) = evenAction a (evenAction b v) := by
    simp only [←Module.End.mul_apply,←map_mul,MulAut.conj_apply,inv_mul_cancel_right]
  have hw' : ∀ s ∈ SylowModel.sylowGroup, evenAction s (evenAction g w) = evenAction g w := by
    intro s hs'
    rw [←hs] at hs'
    obtain ⟨t,ht,rfl⟩ := hs'
    change evenAction (MulAut.conj g t) (evenAction g w) = _
    rw [hc,hw t ht]
  obtain ⟨x,hx,hxn⟩ := seed_mover
  let k := MulAut.conj g⁻¹ x
  have hk : evenAction k w = w := by
    apply (evenAction.apply_bijective g).injective
    have hkx : MulAut.conj g k = x := by simp [k,MulAut.conj_apply,mul_assoc]
    rw [←hc,hkx,hx _ hw']
  have hxN : x ∈ normalizer (A.map (MulAut.conj g).toMonoidHom : Set _) := by
    have hh := (le_normalizer_map (MulAut.conj g).toMonoidHom)
      (mem_map_of_mem (MulAut.conj g).toMonoidHom (hn k hk))
    have he : (MulAut.conj g).toMonoidHom k = x := by
      simp [k,MulAut.conj_apply,mul_assoc]
    exact he ▸ hh
  exact hxn (he ▸ hxN)

/-- A two-subgroup normalized by the point centralizer contains no best
offender when it shares the original Sylow group fixing that point. -/
private theorem no_bestOffender_of_point_normalizes
    (P Q : Subgroup HexAutomorphisms) (hP : IsPGroup 2 P) (hQP : Q ≤ P)
    (S : Sylow 2 HexEvenAutomorphisms)
    (hSP : (S : Subgroup HexEvenAutomorphisms).map hexSign.ker.subtype ≤ P)
    (w : hexacode) (hw : ∀ s ∈ S, evenAction s w = w)
    (hn : ∀ k : HexEvenAutomorphisms, evenAction k w = w → k.val ∈ normalizer (Q : Set _))
    {A : Subgroup HexAutomorphisms} (hAQ : A ≤ Q)
    (hA : IsBestOffender action A) : False := by
  have hAe := Hexacode.bestOffender_le_even A hA
  let Ae := A.subgroupOf hexSign.ker
  have hbest : IsBestOffender evenAction Ae := hA.subgroupOf action hAe
  have hPS : P.comap hexSign.ker.subtype = (S : Subgroup HexEvenAutomorphisms) :=
    S.is_maximal' hP.comap_subtype (by
      intro x hx
      exact hSP (mem_map_of_mem hexSign.ker.subtype hx))
  have hAS : Ae ≤ S := by
    intro x hx
    rw [←hPS]
    exact hQP (hAQ hx)
  apply point_not_normalizes_offender S Ae hAS hbest w hw
  intro k hk
  have hQk := mem_normalizer_iff_map_conj_eq.mp (hn k hk)
  have hAk : A.map (MulAut.conj k.val).toMonoidHom = A :=
    Hexacode.bestOffender_unique_in_pgroup Q (hP.to_le hQP)
      (hQk ▸ map_mono hAQ) hAQ (hA.map_conj action k.val) hA
  apply mem_normalizer_iff.mpr
  intro a
  change a.val ∈ A ↔ k.val*a.val*k.val⁻¹ ∈ A
  exact mem_normalizer_iff.mp (mem_normalizer_iff_map_conj_eq.mpr hAk) a.val

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ExceptionalSixOffenders

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ExceptionalSixOffenders
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender Atlas.Codes
open Representation.Hexacode
open ChapterC
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- The literal Thompson subgroup centralizes U when the point centralizer
normalizes Q. This is the forbidden parabolic/offender configuration. -/
private theorem thompson_le_kernel (X : Subgroup G) [X.Normal]
    (hb : IsExceptionalAhat6Block X) (R Q : Subgroup G)
    (hR : IsPGroup 2 R) (hQR : Q ≤ R)
    (hUQ : (blockU X).map X.subtype ≤ Q)
    (P : Sylow 2 X) (hPR : (P : Subgroup X).map X.subtype ≤ R)
    (u : blockU X) (huR : ((u : X) : G) ∈ centralizer (R : Set G))
    (hn : X ⊓ centralizer ({((u : X) : G)} : Set G) ≤ normalizer (Q : Set G)) :
    elementaryAbelianMaxJ Q ≤ centralizer ((blockU X).map X.subtype : Set G) := by
  let := hb.1.elementary
  obtain ⟨c,E,f,hfx,hE,himage,hker,hWker⟩ := normal_action X hb
  let W := (blockU X).map X.subtype
  let : W.Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_unique ((show (⊤ : Subgroup G) ≤ normalizer (X : Set G) from
      le_normalizer_of_normal).trans (normalizer_le_normalizer_characteristic_image X (blockU X)))
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map X.subtype
  let j : blockU X ≃* W := (blockU X).equivMapOfInjective X.subtype X.subtype_injective
  let e : Additive W ≃ₗ[ZMod 2] hexacode :=
    (LinearEquiv.ofBijective (j.symm.toMonoidHom.toAdditive.toZModLinearMap 2) j.symm.bijective).trans E
  have he (g : G) (w : W) :
      e (Additive.ofMul (MulAut.conjNormal g w)) = action (f g) (e (Additive.ofMul w)) := by
    have hh : j.symm (MulAut.conjNormal g w) =
        MulAut.characteristic (blockU X) (MulAut.conjNormal g) (j.symm w) := by
      apply j.injective
      rw [j.apply_symm_apply]
      apply Subtype.ext
      change g * (w : G) * g⁻¹ = g * (((j.symm w : blockU X) : X) : G) * g⁻¹
      congr 2
      exact (congrArg Subtype.val (j.apply_symm_apply w)).symm
    change E (Additive.ofMul (j.symm (MulAut.conjNormal g w))) = _
    rw [hh]
    exact hE g (j.symm w)
  let q := f.rangeRestrict
  have hq := f.rangeRestrict_surjective
  have hk : q.ker = centralizer (W : Set G) := by
    rw [MonoidHom.ker_rangeRestrict,hWker]
  let ρ := NormalElementaryQuotient.representation W q hq hk
  have heq (g : f.range) (w : Additive W) :
      e (ρ g w) = action g.val (e w) := by
    obtain ⟨g,rfl⟩ := hq g
    have hc : (ρ (q g) w).toMul = MulAut.conjNormal g w.toMul :=
      Subtype.ext (NormalElementaryQuotient.representation_apply W q hq hk g w)
    change e (Additive.ofMul (ρ (q g) w).toMul) = _
    rw [hc]
    exact he g w.toMul
  let S := P.mapSurjective (f := c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X)))
    (c.surjective.comp (QuotientGroup.mk'_surjective _))
  have hSP : (S : Subgroup HexEvenAutomorphisms).map hexSign.ker.subtype ≤ R.map f := by
    rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    change (c (QuotientGroup.mk' (pCore 2 X) x)).val ∈ R.map f
    rw [←hfx x]
    exact mem_map_of_mem f (hPR (mem_map_of_mem X.subtype hx))
  let w := E (Additive.ofMul u)
  have hw : ∀ s ∈ S, evenAction s w = w := by
    rintro _ ⟨x,hx,rfl⟩
    change action (c (QuotientGroup.mk' (pCore 2 X) x)).val (E (Additive.ofMul u)) = E (Additive.ofMul u)
    rw [←hfx x,←hE]
    apply congrArg E
    apply congrArg Additive.ofMul
    apply Subtype.ext
    apply Subtype.ext
    change (x : G)*((u : X) : G)*(x : G)⁻¹ = u
    rw [huR x (hPR (mem_map_of_mem X.subtype hx)),mul_inv_cancel_right]
  have hn' (k : HexEvenAutomorphisms) (hkw : evenAction k w = w) :
      k.val ∈ normalizer (Q.map f : Set HexAutomorphisms) := by
    obtain ⟨x,hx⟩ := c.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 X)) k
    have hfk : f x = k.val := (hfx x).trans (congrArg Subtype.val hx)
    have hxu : (x : G) ∈ centralizer ({((u : X) : G)} : Set G) := by
      have hh := hE x u
      rw [hfk] at hh
      change action k.val (E (Additive.ofMul u)) = E (Additive.ofMul u) at hkw
      rw [hkw] at hh
      have he := congrArg (fun v : Additive (blockU X) => ((v.toMul : X) : G)) (E.injective hh)
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
    rw [←hfk]
    exact le_normalizer_map f (mem_map_of_mem f (hn ⟨x.property,hxu⟩))
  rw [←hWker]
  apply sSup_le
  intro B hB
  apply (map_eq_bot_iff B).mp
  by_contra hne
  have hne' : B.map q ≠ ⊥ := by
    intro hh
    apply hne
    have hm := congrArg (map f.range.subtype) hh
    simpa only [q,map_map,Subgroup.map_bot,MonoidHom.subtype_comp_rangeRestrict] using hm
  have hbest := NormalElementaryQuotient.maxElementary_isBestOffender W q hq hk Q B hUQ hB hne'
  have hoff := (hbest.isOffender ρ).map_equivariant ρ action f.range.subtype f.range.subtype_injective e heq
  have hm : (B.map q).map f.range.subtype = B.map f := by
    rw [map_map,MonoidHom.subtype_comp_rangeRestrict]
  rw [hm] at hoff
  obtain ⟨A,hAB,hbestA⟩ := hoff.exists_bestOffender action
  exact no_bestOffender_of_point_normalizes (R.map f) (Q.map f) (hR.map f)
    (map_mono hQR) S hSP w hw hn' (hAB.trans (map_mono hB.1)) hbestA

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ExceptionalSixOffenders

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ExceptionalSixOffenders
open Subgroup Theory.GroupTheory ChapterC

private theorem exceptional_transport {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : IsExceptionalAhat6Block A) : IsExceptionalAhat6Block B := by
  let a := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hu := RankOne.Solvable.blockU_map_equiv e
  let u := (e.subgroupMap (blockU A)).trans (MulEquiv.subgroupCongr hu)
  let := h.2.1
  refine ⟨RankOne.Solvable.isShort_of_equiv e h.1,
    IsQuasisimple.of_mulEquiv a,?_,?_,?_,?_⟩
  · exact (Nat.card_congr (centerCongr a).symm.toEquiv).trans h.2.2.1
  · obtain ⟨c⟩ := h.2.2.2.1
    exact ⟨(QuotientGroup.congr _ _ a (Theory.GroupTheory.FixedElementary.map_center a)).symm.trans c⟩
  · exact (Nat.card_congr u.symm.toEquiv).trans h.2.2.2.2.1
  · rw [←hu,←Theory.Quasithin.map_centralizer e, h.centralizer,pCore_map_iso]

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData.ExceptionalSixOffenders

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Stellmacher ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open ExceptionalSixOffenders
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The exceptional cubic block contradicts the original C.2.7 offender.
The literal Q₁ and the original central-involution seed are retained. -/
theorem localFamily_not_exceptionalSix_of_input
    (d : CaseIComponentData T M Mc V) (h : PreparedChosenModule T M V)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hQS : d.Q1 ≤ d.S)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ K) :
    ¬ IsExceptionalAhat6Block K := by
  intro hb
  obtain ⟨_,_,_,u,_,_,huR,huC⟩ :=
    d.localFamily_exceptionalSix_point h hTM hu hK hi.quasisimple hi.outside hb
  let R := d.normalizerSylow K
  let H := K ⊔ R
  let X := K.subgroupOf H
  let Q := d.Q1.subgroupOf H
  let R0 := R.subgroupOf H
  have hQR : d.Q1 ≤ R := le_inf hQS hi.normalizes
  have hQH : d.Q1 ≤ H := hQR.trans le_sup_right
  let : X.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  let e : X ≃* K := subgroupOfEquivOfLe le_sup_left
  let eU : blockU X ≃* blockU K := (e.subgroupMap _).trans
    (MulEquiv.subgroupCongr (RankOne.Solvable.blockU_map_equiv e))
  have hb0 := ExceptionalSixOffenders.exceptional_transport e.symm hb
  let u0 := eU.symm u
  have hu0 : (((u0 : X) : H) : G) = ((u : K) : G) :=
    congrArg (fun v : blockU K => ((v : K) : G)) (eU.apply_symm_apply u)
  have hcore : (K ⊔ d.Q1).pCoreIn 2 ≤ d.Q1 := by
    let : (K.subgroupOf (K ⊔ d.Q1)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hi.normalizes)
    exact source_joinCore_le_radical (source_join_input hi)
  have hUQ : (blockU K).map K.subtype ≤ d.Q1 :=
    (map_mono (blockU_le_core (L := K))).trans
      ((pCoreIn_mono_of_normalizes le_sup_left (sup_le le_normalizer hi.normalizes)).trans hcore)
  have hUQ0 : (blockU X).map X.subtype ≤ Q := by
    rintro _ ⟨v,hv,rfl⟩
    exact hUQ (mem_map_of_mem K.subtype
      (show e v ∈ blockU K from (eU ⟨v,hv⟩).property))
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hK.2
  let P0 := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hPR : (P0 : Subgroup X).map X.subtype ≤ R0 := by
    rintro _ ⟨_,⟨k,hk,rfl⟩,rfl⟩
    have hs : (k : G) ∈ d.S := (hP ▸ mem_map_of_mem K.subtype hk).1
    exact ⟨hs,le_normalizer k.property⟩
  have hR : IsPGroup 2 R0 := (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)).comap_subtype
  have hfix : ((u0 : X) : H) ∈ centralizer (R0 : Set H) := by
    intro r hr
    apply Subtype.ext
    change (r : G)*(((u0 : X) : H) : G) = (((u0 : X) : H) : G)*r
    rw [hu0]
    exact huR r hr
  have hn : X ⊓ centralizer ({((u0 : X) : H)} : Set H) ≤ normalizer (Q : Set H) := by
    intro k hk
    have hkC : (k : G) ∈ centralizer ({((u : K) : G)} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hk.2)
      simpa only [Subgroup.coe_mul,hu0] using hh
    have hkM := (huC ⟨hk.1,hkC⟩).1
    have hkN : (k : G) ∈ normalizer (d.Q1 : Set G) :=
      (d.MZ.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.MZ (pCore 2 d.MZ))) hkM
    apply mem_normalizer_iff.mpr
    intro q
    exact mem_normalizer_iff.mp hkN (q : G)
  have hJ := thompson_le_kernel X hb0 R0 Q hR (fun _ hx => hQR hx) hUQ0 P0 hPR u0 hfix hn
  let := hb0.1.elementary
  obtain ⟨_,_,f,_,_,_,hk,hker⟩ := normal_action X hb0
  rw [←hker] at hJ
  have hc := inf_ker_le_core_of_two_supplement f X Q le_normalizer_of_normal
    (hR.to_le (fun _ hx => hQR hx)) (hk ▸ pCore_isPGroup)
  have hJcore := (le_inf ((sSup_le fun _ hA => hA.1).trans le_sup_right) hJ).trans hc
  have hm := map_mono (f := H.subtype) hJcore
  rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hQH,
    map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
    map_subgroupOf_eq_of_le hQH] at hm
  have he := elementaryAbelianMaxJ_eq_of_intermediate d.Q1 ((K ⊔ d.Q1).pCoreIn 2) hm hcore
  exact (kernel_offender_from_source hi).2.thompson he.ge

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup Theory.GroupTheory Stellmacher ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The original selected component cannot be the exceptional cubic A₆ block,
for either original source prime. Q₁-normalization is proved from its central quotient. -/
theorem PreExclusionSource.not_constrained_exceptionalSix
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    ¬ IsExceptionalAhat6Block d.L := by
  intro hb
  obtain ⟨e⟩ := hb.2.2.2.1
  let a := (centralPreimageQuotientEquiv (pCore 2 d.L)).trans e
  have hi := (s.constrained_alternating_central_input (h := h) hG hu hb.1.fitting (by decide) a).2
  exact d.localFamily_not_exceptionalSix_of_input h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩
    (d.catalogue_radical_le_sylow s.centralizer_sylow hu) hi hb

/-- The same cubic-block exclusion after exchanged selection, with the
original component, radical and seed unchanged. -/
theorem ExchangedSource.not_constrained_exceptionalSix
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) : ¬ IsExceptionalAhat6Block d.L := by
  intro hb
  obtain ⟨e⟩ := hb.2.2.2.1
  let a := (centralPreimageQuotientEquiv (pCore 2 d.L)).trans e
  have hK : d.L ∈ Chapter1.LIn d.G1 d.S := ⟨d.L_component.1,s.local_component⟩
  have hN := d.localFamily_alternating_central_normalizes hG h hK hb.2.1 (by decide) a
  have hQS := d.catalogue_radical_le_sylow s.centralizer_sylow hu
  have hi := s.constrained_input_of_normalizes hG h hb.1.fitting (hQS.trans hN)
  exact d.localFamily_not_exceptionalSix_of_input h hM.1.2 hu hK hQS hi hb

/-- Removing the actual cubic offender closes the selected constrained catalogue
conditional only on its independently owned whole-core reconstruction and earlier residual input. -/
theorem PreExclusionSource.constrained_catalogue_of_reconstruction
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    (hf : generalizedFitting d.L = pCore 2 d.L) : d.ConstrainedAlternatives := by
  exact (s.constrained_catalogue_or_exceptional_six_of_reconstruction (h := h)
    ha hG hempty hM hJ hu hne hmany hfull hres hf).resolve_right
      (fun he => s.not_constrained_exceptionalSix (h := h) hG hM hu he.1)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Stellmacher ChapterC
open Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original-marker application of the cubic-block exclusion, retaining both
source primes and the genuine earlier 15.1.14 residual premise. -/
theorem PreparedChosenModule.source_preExclusion_not_exceptionalSix
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧ ¬ IsExceptionalAhat6Block d.L := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,s.not_constrained_exceptionalSix (h := h) hG hM hu⟩

/-- The original constrained catalogue on the same selected component and
marker. The independent A₆ reconstruction remains explicit for final assembly. -/
theorem PreparedChosenModule.source_preExclusion_constrained_catalogue_of_reconstruction
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L → d.ConstrainedAlternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,s.constrained_catalogue_of_reconstruction (h := h)
    ha hG hempty hM hJ hu hne hmany hfull hres⟩

end CFSG.Quasithin.Chapter15.Section01

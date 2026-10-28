module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.FullFixedLift
public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.AfterNormalizer
import all CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.NormalizerExtension.SourceCompletion.Nonsplit.TwoClasses

/-!
# Marked fixed-centralizer transport to the original ambient group

Compose the literal fixed-normalizer isomorphism with the given Aut(A6) marking.
The evaluation formula retains the actual quotient map; the final inclusion
places the fixed subgroup in the original ambient involution centralizer.

Source: Aschbacher–Smith J.2.9, printed p.438.
-/

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

noncomputable def centralizerMapEquiv {X Y : Type*} [Group X] [Group Y]
    (e : X≃*Y) (x:X) : centralizer ({x}:Set X)≃*centralizer ({e x}:Set Y) where
  toFun a := ⟨e a,mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp a.property))⟩
  invFun a := ⟨e.symm a,mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using mem_centralizer_singleton_iff.mp a.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv a := Subtype.ext (e.apply_symm_apply a)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

public noncomputable def markedFixedEquiv
    (e : c.NormalizerQuotient≃*AlternatingSix.ShadowLocal.AutA6)
    (u : c.NB) (hu : c.InvertsB (u:G)) :
    centralizer ({u}:Set c.NB)≃*
      centralizer ({e (c.normalizerQuotientMap u)}:Set AlternatingSix.ShadowLocal.AutA6) :=
  (c.normalizerFixedEquiv u hu).trans (centralizerMapEquiv e (c.normalizerQuotientMap u))

public theorem markedFixedEquiv_apply
    (e : c.NormalizerQuotient≃*AlternatingSix.ShadowLocal.AutA6)
    (u : c.NB) (hu : c.InvertsB (u:G)) (x : centralizer ({u}:Set c.NB)) :
    (c.markedFixedEquiv e u hu x : AlternatingSix.ShadowLocal.AutA6)=
      e (c.normalizerQuotientMap x) := by
  exact congrArg e (c.normalizerFixedEquiv_apply u hu x)

public noncomputable def fixedAmbientMap (u:c.NB) :
    centralizer ({u}:Set c.NB)→*centralizer ({(u:G)}:Set G) where
  toFun x := ⟨x,mem_centralizer_singleton_iff.mpr
    (congrArg (fun a:c.NB => (a:G)) (mem_centralizer_singleton_iff.mp x.property))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

public theorem fixedAmbientMap_apply (u:c.NB) (x:centralizer ({u}:Set c.NB)) :
    (c.fixedAmbientMap u x : G) = ((x:c.NB):G) := by
  rfl

public theorem fixedAmbientMap_injective (u:c.NB) : Function.Injective (c.fixedAmbientMap u) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun a : centralizer ({(u:G)}:Set G) => (a:G)) h

end CFSG.Quasithin.ChapterJ.Centralizers.Choices

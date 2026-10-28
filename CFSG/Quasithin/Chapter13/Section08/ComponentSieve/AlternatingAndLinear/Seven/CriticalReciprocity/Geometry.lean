module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Endpoint
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Transport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Actors

/-!
# The corrected reciprocal marking and its two-core placement

The printed β := γ g_b⁻¹ on p.958 returns γ to γ₁ under the earlier edge
marking. The reciprocal subgroup used by the proof is instead U_H^{g_b⁻¹}
inside V_H^{g_b⁻¹}, attached to β := γ₁ g_b⁻¹. We use that corrected vertex
and literal subgroup conjugates throughout. In particular the returned Uγ
is U_H, not the reciprocal actor Uβ.

F.9.13(2) places V_H in the terminal edge's intrinsic two-core. Inverse
conjugation returns that edge to L₁T, placing Vβ directly in O₂(L₁T).
The quotient by O₂(H) carries this to the literal two-core of (L₁T)*.
All normality and two-cores are relative to the indicated local groups.

Source: Aschbacher–Smith, F.9.13(1–2), printed p.322, and 13.8.24,
printed pp.958–959 (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.CriticalReciprocity
open CriticalGeometry
variable {G : Type*} [Group G] {L T H V : Subgroup G}

abbrev beta (c : CriticalPair L T H V) : Vertex L T H :=
  AsymmetricPair.returnElement c • base L T H true

def Ubeta (c : CriticalPair L T H V) (V₃ : Subgroup G) : Subgroup G :=
  (Source.UH H V₃).conjBy (c.gb : G)⁻¹

def Vbeta (c : CriticalPair L T H V) : Subgroup G :=
  (Source.VH H V).conjBy (c.gb : G)⁻¹

theorem return_gamma (c : CriticalPair L T H V) :
    AsymmetricPair.returnElement c • c.gamma = base L T H true :=
  AsymmetricPair.returnElement_gamma c

theorem vertexGroup_beta (c : CriticalPair L T H V) :
    vertexGroup L T H (beta c) = H.conjBy (c.gb : G)⁻¹ :=
  AsymmetricPair.vertexGroup_alpha c

theorem returned_Ugamma (c : CriticalPair L T H V) (V₃ : Subgroup G) :
    (c.Ugamma V₃).conjBy (c.gb : G)⁻¹ = Source.UH H V₃ :=
  conjBy_inv _ _

theorem returned_Aone (c : CriticalPair L T H V) (V₁ : Subgroup G) :
    (c.Aone V₁).conjBy (c.gb : G)⁻¹ = V₁ := conjBy_inv _ _

theorem Ubeta_le_Vbeta (c : CriticalPair L T H V) (V₃ : Subgroup G)
    (hV₃V : V₃ ≤ V) : Ubeta c V₃ ≤ Vbeta c :=
  map_mono (conjugateSpanBy_mono hV₃V le_rfl)

theorem Vbeta_le_twoCore [Finite G] (c : CriticalPair L T H V)
    (L₁ : Subgroup G) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hV : Source.VH H V ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2) :
    Vbeta c ≤ (L₁ ⊔ T).pCoreIn 2 := by
  have hh := map_mono (f := (MulAut.conj (c.gb : G)⁻¹).toMonoidHom) hV
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj (c.gb : G)⁻¹).injective,
    c.edgeGroup_eq L₁ he] at hh
  change Vbeta c ≤ ((L₁ ⊔ T).conjBy (c.gb : G) |>.conjBy (c.gb : G)⁻¹).pCoreIn 2 at hh
  rwa [conjBy_inv] at hh

theorem Vbeta_le_H [Finite G] (c : CriticalPair L T H V)
    (L₁ : Subgroup G) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hV : Source.VH H V ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2) :
    Vbeta c ≤ H :=
  (Vbeta_le_twoCore c L₁ he hV).trans ((pCoreIn_le 2 _).trans
    (he ▸ inf_le_right))

theorem star_Vbeta_le_twoCore [Finite G] (c : CriticalPair L T H V)
    (L₁ : Subgroup G) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hV : Source.VH H V ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2) :
    Source.starImage H (Vbeta c) ≤ (Source.starImage H (L₁ ⊔ T)).pCoreIn 2 := by
  rw [← LocalGeometry.starImage_twoCore H (L₁ ⊔ T) (he ▸ inf_le_right)]
  exact LocalGeometry.starImage_mono H (Vbeta_le_twoCore c L₁ he hV)

/-- A compatible partition marking carries Vβ* into the actual Klein-four
two-core of the four-plus-three stabilizer. -/
theorem mapped_Vbeta_le_partitionCore [Finite G] (c : CriticalPair L T H V)
    (L₁ : Subgroup G) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hV : Source.VH H V ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hp : (Source.starImage H (L₁ ⊔ T)).map φ = fourThreeStabilizer) :
    (Source.starImage H (Vbeta c)).map φ ≤ fourThreeStabilizer.pCoreIn 2 := by
  have hh := map_mono (f := φ) (star_Vbeta_le_twoCore c L₁ he hV)
  rwa [map_pCoreIn_of_injective 2 _ _ hφ, hp] at hh


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.CriticalReciprocity

end

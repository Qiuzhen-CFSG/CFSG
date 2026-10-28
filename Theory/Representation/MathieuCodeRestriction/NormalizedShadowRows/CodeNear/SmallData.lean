module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeNear.Data
/-! Five-dimensional displacement witnesses outside the four-element
centralizer of the marked inner involution's code fixed space.
Source: Aschbacher--Smith H.16.2(5), H.16.5, printed pp.402--404. -/
@[expose] public section
namespace MathieuCode.NormalizedShadowRows.CodeNear
open Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.OrderEnumeration
open MathieuCode.QuadraticActors
set_option maxRecDepth 4096
set_option Elab.async false

def smallTable : Table Nat 7 :=
(((((((0, 75597644022522684085377), (43684787189581240046721, 0)), ((2365223534625198150785, 0), (327026765747183868417153, 0))), (((43700341215317348029569, 0), (43700351629893436675201, 0)), ((2364070049895759975553, 0), (2365223534625332368513, 0)))), ((((157092514490869633750145, 43700341220402589308033), (157092514490869633750145, 0)), ((2364070050170772100225, 0), (2364070050170637882497, 0))), (((157092514490869633750145, 0), (43684787189579293889665, 0)), ((157092514490861245142145, 0), (2365223534350320243841, 0))))), (((((43700351634978677953665, 43684787194664539362433), (43700341220402589308033, 0)), ((43700341215317348029569, 0), (2365223534625198150785, 0))), (((157092477036409961813121, 0), (43700341215317348029569, 0)), ((75597662036921193567361, 0), (43684776780092343030913, 0)))), ((((43684787194666481325185, 43684787194664535168129), (0, 0)), ((43700351629891486323841, 0), (43700341215317348029569, 0))), (((2364070050170637882497, 0), (327026834746641804924033, 0)), ((43700341215317352223873, 0), (157092514490861245142145, 0)))))), ((((((157021572363876640724097, 157021572363885029332097), (43700341220402589308033, 0)), ((2365223534625198150785, 0), (43684787194666481325185, 0))), (((43700341215317348029569, 0), (43684787189579298083969, 0)), ((157021572363885029332097, 0), (2365223534625332368513, 0)))), ((((43700341220402593502337, 43684787189581240046721), (75560750534375264982145, 0)), ((2364070050170772100225, 0), (2364070050170637882497, 0))), (((43700341215317348029569, 0), (43684787194666481325185, 0)), ((43684776775007105946753, 0), (0, 0))))), (((((75560768548773774464129, 43700341220402589308033), (43684776775005155595393, 0)), ((75560750534379555755137, 0), (2364070050170637882497, 0))), (((75597644031318772913281, 0), (43700341215317348029569, 0)), ((0, 0), (2364070049895759975553, 0)))), ((((43684787189579293889665, 43684776775005155595393), (157021572363876640724097, 0)), ((2365223534350320243841, 0), (75560750534379555755137, 0))), (((2365223534625198150785, 0), (75597644031318772913281, 0)), ((43684787194664535168129, 0), (43684776780092347225217, 0)))))))

def smallSet : Finset (Fin 72) := {0,27,38,61}
def smallColumn (v : Fin 72) (j : Fin 5) : Nat := (lookup 7 smallTable v.val >>> (5*j.val)) % 32
def smallSelected (v : Fin 72) : Matrix (Fin 11) (Fin 5) (ZMod 2) :=
  fun i j => quotientMatrix (if smallColumn v j < 11 then 27 else v) i
    ⟨smallColumn v j % 11, Nat.mod_lt _ (by decide)⟩
def smallLeft (v : Fin 72) : Matrix (Fin 5) (Fin 11) (ZMod 2) :=
  fun i j => bit (lookup 7 smallTable v.val) (25+11*i.val+j.val)
def smallCheck (v : Fin 72) : Prop := v ∉ smallSet → smallLeft v * smallSelected v = 1

private theorem small0 : ∀ a : Fin 8, smallCheck ⟨8*0+a.val,by omega⟩ := by
  unfold smallCheck
  decide +kernel

private theorem small1 : ∀ a : Fin 8, smallCheck ⟨8*1+a.val,by omega⟩ := by
  unfold smallCheck
  decide +kernel

private theorem small2 : ∀ a : Fin 8, smallCheck ⟨8*2+a.val,by omega⟩ := by
  unfold smallCheck
  decide +kernel

private theorem small3 : ∀ a : Fin 8, smallCheck ⟨8*3+a.val,by omega⟩ := by
  unfold smallCheck
  decide +kernel

private theorem small4 : ∀ a : Fin 8, smallCheck ⟨8*4+a.val,by omega⟩ := by
  unfold smallCheck
  decide +kernel

private theorem small5 : ∀ a : Fin 8, smallCheck ⟨8*5+a.val,by omega⟩ := by
  unfold smallCheck
  decide +kernel

private theorem small6 : ∀ a : Fin 8, smallCheck ⟨8*6+a.val,by omega⟩ := by
  unfold smallCheck
  decide +kernel

private theorem small7 : ∀ a : Fin 8, smallCheck ⟨8*7+a.val,by omega⟩ := by
  unfold smallCheck
  decide +kernel

private theorem small8 : ∀ a : Fin 8, smallCheck ⟨8*8+a.val,by omega⟩ := by
  unfold smallCheck
  decide +kernel

theorem small_checked (v : Fin 72) : smallCheck v := by
  have blocks : ∀ k : Fin 9, ∀ a : Fin 8, smallCheck ⟨8*k.val+a.val,by omega⟩ := by
    intro k
    fin_cases k
    · exact small0
    · exact small1
    · exact small2
    · exact small3
    · exact small4
    · exact small5
    · exact small6
    · exact small7
    · exact small8
  have h := blocks ⟨v.val/8,by omega⟩ ⟨v.val%8,by omega⟩
  have he : (⟨8*(v.val/8)+v.val%8,by omega⟩ : Fin 72) = v := by
    apply Fin.ext
    change 8*(v.val/8)+v.val%8 = v.val
    omega
  rwa [he] at h
end MathieuCode.NormalizedShadowRows.CodeNear

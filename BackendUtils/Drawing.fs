(*

Copyright 2012-2013 Jack Pappas

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*)

//
module BackendUtils.Drawing


/// Functions for generating color palettes.
// Reference : http://martin.ankerl.com/2009/12/09/how-to-create-random-colors-programmatically/
[<RequireQualifiedAccess>]
module Palette =
    open System.Drawing

    /// The conjugate of the golden ratio.
    let private phi_conj = ((1.0 + sqrt 5.0) / 2.0) - 1.0

    //
    let private colorFromHSV (hue : float, saturation : float, brightness : float) : Color =
        // Preconditions
        if hue < 0.0 || hue > 360.0 then
            invalidArg "hue" "The hue must be between 0.0 and 360.0 degrees."
        elif saturation < 0.0 || saturation > 1.0 then
            invalidArg "saturation" "The saturation must be in the range [0.0, 1.0]."
        elif brightness < 0.0 || brightness > 1.0 then
            invalidArg "brightness" "The brightness value must be in the range [0.0, 1.0]."

        let chroma = saturation * brightness
        
        let r', g', b' =
            let hue' = hue / 60.0
            let x =
                chroma * (1.0 - abs ((hue' % 2.0) - 1.0))

            if hue' < 0.0 then
                // This shouldn't ever happen, but just to be sure...
                0.0, 0.0, 0.0
            elif hue' < 1.0 then
                chroma, x, 0.0
            elif hue' < 2.0 then
                x, chroma, 0.0
            elif hue' < 3.0 then
                0.0, chroma, x
            elif hue' < 4.0 then
                0.0, x, chroma
            elif hue' < 5.0 then
                x, 0.0, chroma
            else // x >= 5 && x < 6
                chroma, 0.0, x

        let m = brightness - chroma

        Color.FromArgb (
            int ((r' + m) * 255.0),
            int ((g' + m) * 255.0),
            int ((b' + m) * 255.0))

    /// Returns a randomly-generated color palette
    /// with the specified number of colors.
    let random count =
        // Preconditions
        // TODO : Count must be non-negative.

        // TODO : If the count is zero return an empty array.

        let rng = System.Random ()
        // Create the random hue value for each color.
        Array.init count <| fun _ -> rng.NextDouble ()
        |> Array.map (fun hue ->
            // The saturation and brightness values can be tweaked as desired.
            let h = (hue + phi_conj) % 1.0
            colorFromHSV (h * 360.0, 0.5, 0.95))

